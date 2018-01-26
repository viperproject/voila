/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import java.io.File
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, Paths}

import scala.collection.breakOut
import scala.util.{Left, Right}
import ch.qos.logback.classic.{Level, Logger}
import com.typesafe.scalalogging.StrictLogging
import org.apache.commons.io.FileUtils
import org.bitbucket.inkytonik.kiama.util.Positions
import org.slf4j.LoggerFactory
import viper.silver
import viper.voila.backends.{MockViperFrontend, Silicon, ViperNameSanitizer}
import viper.voila.frontend._
import viper.voila.reporting._
import viper.voila.translator.{ErrorBacktranslator, PProgramToViperTranslator}

object VoilaConstants {
  val toolName = "Voila"
  val toolVersion = "0.1"
  val toolCopyright = "(c) Copyright ETH Zurich 2016"

  val versionMessage = s"${VoilaConstants.toolName} ${VoilaConstants.toolVersion} ${VoilaConstants.toolCopyright}"

  val preambleFile = "/preamble.vpr"
}

object VoilaGlobalState {
  var positions: Positions = _
}

class Voila extends StrictLogging {
  val defaultPreambleFile: Path = {
    val resource = getClass.getResource(VoilaConstants.preambleFile)

    if (resource == null)
      exitWithError(s"Cannot access resource ${VoilaConstants.preambleFile}")

    val file = silver.utility.Paths.pathFromResource(resource)

    if (!Files.isRegularFile(file)) exitWithError(s"$file is not a file")
    if (!Files.isReadable(file)) exitWithError(s"Cannot read from $file")

    file
  }

  lazy val defaultPreamble: Option[silver.ast.Program] = {
    val preambleFile = defaultPreambleFile
    val viperFrontend = new MockViperFrontend()

    viperFrontend.translate(preambleFile) match {
      case (None, errors) =>
        logger.error(s"Could not parse Viper preamble $preambleFile:")
        errors foreach (error => logger.error(s"  ${error.readableMessage}"))
        None
      case (Some(viperProgram), Seq()) =>
        Some(viperProgram)
    }
  }

  def verify(config: Config): Option[VoilaResult] = {
    verify(Paths.get(config.inputFileName()), config)
  }

  def verify(file: String): Option[VoilaResult] = {
    val config = new Config(Array("-i", file))

    verify(Paths.get(config.inputFileName()), config)
  }

  def verify(path: Path): Option[VoilaResult] = {
    val config = new Config(Array("-i", path.toFile.getPath))

    verify(Paths.get(config.inputFileName()), config)
  }

  def verify(file: Path, config: Config): Option[VoilaResult] = {
    setLogLevelsFromConfig(config)

    logger.info(VoilaConstants.versionMessage)

    if (!Files.isRegularFile(file)) exitWithError(s"${config.inputFileName()} is not a file")
    if (!Files.isReadable(file)) exitWithError(s"Cannot read from ${config.inputFileName()}")

    logger.debug(s"Reading source program from file ${config.inputFileName()}")

    val frontend = new Frontend()

    VoilaGlobalState.positions = frontend.positions // TODO: Remove global state

    frontend.parse(file) match {
      case Left(voilaErrors) =>
        Some(Failure(voilaErrors))

      case Right(program) =>
        /* TODO: Move semantic analysis to the frontend */

        logger.info("Parsed")
        logger.info(s"  ${program.regions.length} region(s): ${program.regions.map(_.id.name).mkString(", ")}")
        logger.info(s"  ${program.predicates.length} predicate(s): ${program.predicates.map(_.id.name).mkString(", ")}")
        logger.info(s"  ${program.procedures.length} procedures(s): ${program.procedures.map(_.id.name).mkString(", ")}")

        /* Pretty-print the parsed and desugared Voila program back to a file, if requested */
        config.outputParsedProgramFileName.map(new File(_)).foreach(outputFile => {
          logger.info(
             "Writing parsed and desugared input program back to file " +
            s"${config.outputParsedProgramFileName()}")

          FileUtils.writeStringToFile(outputFile, program.pretty, UTF_8)
        })

        if (config.include.supplied) {
          val excludedProcedures: Vector[String] =
            program.procedures
              .map(_.id.name)
              .filterNot(config.include().contains)

          if (excludedProcedures.nonEmpty) {
            logger.warn(
              "The following procedures have been excluded from verification: " +
              excludedProcedures.mkString(", "))
          }
        }

        val tree = new VoilaTree(program)

        var stop = false
        tree.nodes foreach (n => {
          frontend.positions.getStart(n) match {
            case Some(_) => /* OK, nothing to do */
            case None =>
              stop = true
              logger.error(s"### NO POSITION FOR ${n.getClass.getSimpleName}:\n  $n")
          }
        })
        if (stop) exitWithError("Position problems!", 10)

        val semanticAnalyser = new SemanticAnalyser(tree)
        val messages = semanticAnalyser.errors

        if (messages.nonEmpty) {
          val voilaErrors = frontend.translateToVoilaErrors(messages, TypecheckerError)

          return Some(Failure(voilaErrors))
        }

        val nameSanitizer = new ViperNameSanitizer()

        val translator = new PProgramToViperTranslator(config, semanticAnalyser, nameSanitizer)
        val (translatedProgram, errorBacktranslator) = translator.translate(tree)

        logger.debug(s"Taking Viper preamble from ${defaultPreambleFile.toString}")

        val preambleProgram =
          defaultPreamble match {
            case None =>
              val msg = s"Could not parse Viper preamble ${defaultPreambleFile.toString}"

              return Some(Failure(Vector(ResourceError(msg))))

            case Some(preamble) =>
              preamble
          }

        val programToVerify =
          translatedProgram.copy(
            domains = preambleProgram.domains ++ translatedProgram.domains,
            fields = preambleProgram.fields ++ translatedProgram.fields,
            functions = preambleProgram.functions ++ translatedProgram.functions,
            predicates = preambleProgram.predicates ++ translatedProgram.predicates,
            methods = preambleProgram.methods ++ translatedProgram.methods
          )(translatedProgram.pos, translatedProgram.info, translatedProgram.errT)

        /* Pretty-print the generated Viper program to a file, if requested */
        config.outputFileName.map(new File(_)).foreach(outputFile => {
          logger.debug(s"Writing generated program to file ${config.outputFileName()}")

          FileUtils.writeStringToFile(
            outputFile,
            silver.ast.pretty.FastPrettyPrinter.pretty(programToVerify),
            UTF_8)
        })

        programToVerify.checkTransitively match {
          case Seq() => /* No errors, all good */
          case _errors =>
            /* TODO: Generated program yields unexpected consistency errors about
             *       undeclared labels. Find out, why. Could be a Viper error.
             */
            val errors =
              _errors.filterNot(_.readableMessage.contains("found of type Label."))

            if (errors.nonEmpty) {
              logger.error(s"Generated Viper program has ${errors.length} error(s):")
              errors foreach (e => logger.error(s"  ${e.readableMessage}"))

              /* TODO: Return Voila errors instead */
              return Some(Failure(Vector.empty))
            }
        }

        var siliconOptions: Vector[String] = Vector.empty
//        siliconOptions ++= Vector("--numberOfParallelVerifiers", "1")
        siliconOptions ++= Vector("--logLevel", "ERROR")

        logger.info("Encoded Voila program in Viper")
        logger.info("Verifying encoding using Silicon ...")
        val silicon = new Silicon(siliconOptions)

        silicon.start()
        val verificationResult = silicon.handle(programToVerify)
        silicon.stop()
        logger.info(s"... done (with ${getNumberOfErrors(verificationResult)} Viper error(s))")

        backtranslateOrReportErrors(verificationResult, errorBacktranslator)
    }
  }

  private def getNumberOfErrors(verificationResult: silver.verifier.VerificationResult): Int = {
    verificationResult match {
      case silver.verifier.Success => 0
      case silver.verifier.Failure(errors) => errors.length
    }
  }

  private def extractVerificationFailures(failure: silver.verifier.Failure)
                                         : (Seq[silver.verifier.VerificationError],
                                            Seq[silver.verifier.AbstractError]) = {

    failure.errors
      .partition(_.isInstanceOf[silver.verifier.VerificationError])
      .asInstanceOf[(Seq[silver.verifier.VerificationError], Seq[silver.verifier.AbstractError])]
  }

  private def backtranslateOrReportErrors(verificationResult: silver.verifier.VerificationResult,
                                          errorBacktranslator: ErrorBacktranslator)
                                         : Option[VoilaResult] = {

    verificationResult match {
      case silver.verifier.Success =>
        Some(Success)
      case failure: silver.verifier.Failure =>
        extractVerificationFailures(failure) match {
          case (Seq(), viperErrors) =>
            /* No verification failures, but, e.g. type-checking failures */
            logger.error("Found non-verification-failures:")
            viperErrors foreach (ve => logger.error(s"  ${ve.readableMessage}"))

            None

          case (viperErrors, Seq()) =>
            /* Only verification failures */
            val voilaErrors: Vector[VoilaError] =
              viperErrors.flatMap(viperError =>
                errorBacktranslator.translate(viperError) match {
                  case None =>
                    /* Back-translation didn't work */
                    logger.error("Failed to back-translate a Viper error")
                    logger.error(s"  ${viperError.readableMessage}")
                    logger.debug(s"    error is ${viperError.getClass.getSimpleName}")
                    logger.debug(s"    error off. node = ${viperError.offendingNode}")
                    logger.debug(s"    error off. node src = ${translator.Source.unapply(viperError.offendingNode)}")
                    logger.debug(s"    reason is ${viperError.reason.getClass.getSimpleName}")
                    logger.debug(s"    reason off. node = ${viperError.reason.offendingNode}")
                    logger.debug(s"    reason off. node src = ${translator.Source.unapply(viperError.reason.offendingNode)}")


                    None

                  case Some(voilaError) =>
                    Some(voilaError)
                })(breakOut)

            Some(Failure(voilaErrors))
        }
    }
  }

  private def setLogLevelsFromConfig(config: Config) {
    val logger = LoggerFactory.getLogger(this.getClass.getPackage.getName).asInstanceOf[Logger]
    logger.setLevel(Level.toLevel(config.logLevel()))
  }


  def exitWithError(message: String, exitCode: Int = 1): Unit = {
    logger.error(message)

    sys.exit(exitCode)
  }
}

object VoilaRunner extends Voila {
  def main(args: Array[String]) {
    verify(new Config(args)) match {
      case None =>
        exitWithError("Voila failed unexpectedly")
      case Some(result) =>
        result match {
          case Success =>
            logger.info("Voila found no errors")
          case Failure(errors) =>
            logger.error(s"Voila found ${errors.length} error(s):")
            errors foreach (e => logger.error(s"  ${e.formattedMessage}"))
        }
    }
  }
}
