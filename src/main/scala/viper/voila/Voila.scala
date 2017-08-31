/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import java.io.File
import java.nio.charset.StandardCharsets.UTF_8
import ch.qos.logback.classic.{Level, Logger}
import scala.util.{Left, Right}
import com.typesafe.scalalogging.StrictLogging
import org.apache.commons.io.FileUtils
import org.bitbucket.inkytonik.kiama.util.Positions
import org.slf4j.LoggerFactory
import viper.silver
import viper.voila.frontend.{Config, Frontend, SemanticAnalyser, VoilaTree}
import viper.voila.translator.PProgramToViperTranslator
import viper.voila.backends.Silicon
import viper.voila.reporting.VoilaResult

object VoilaConstants {
  val toolName = "Voila"
  val toolVersion = "0.1"
  val toolCopyright = "(c) Copyright ETH Zurich 2016"

  val versionMessage = s"${VoilaConstants.toolName} ${VoilaConstants.toolVersion} ${VoilaConstants.toolCopyright}"

  val preambleFile = "/preamble.vpr"
}

object VoilaGlobalState {
  var positions: Positions = null
}

class Voila {
  def run(args: Array[String]): Unit = ???

  def run(config: Config): Unit = ???

  def verify(file: String): VoilaResult = verify(new File(file))

  def verify(file: File): VoilaResult = {
    val frontend = new Frontend()

    VoilaGlobalState.positions = frontend.positions // TODO: Remove global state

    frontend.parse(FileUtils.readFileToString(file, UTF_8)) match {
      case Left(messages) =>
        frontend.reportErrors(
          s"Parsing $file failed with ${messages.length} error(s):",
          messages)

        sys.exit(1)

      case Right(program) =>
        /* TODO: Move semantic analysis to the frontend */

        logger.info("Parsed")
        logger.info(s"  ${program.regions.length} region(s): ${program.regions.map(_.id.name).mkString(", ")}")
        logger.info(s"  ${program.predicates.length} predicate(s): ${program.predicates.map(_.id.name).mkString(", ")}")
        logger.info(s"  ${program.procedures.length} procedures(s): ${program.procedures.map(_.id.name).mkString(", ")}")

        val tree = new VoilaTree(program)
        val semanticAnalyser = new SemanticAnalyser(tree)
        val messages = semanticAnalyser.errors

        if (messages.nonEmpty) {
          frontend.reportErrors(
            s"Type-checking ${config.inputFile()} failed with ${messages.length} error(s):",
            messages)

          sys.exit(1)
        }

        val translator = new PProgramToViperTranslator(semanticAnalyser)
        val (viperProgram, errorBacktranslator) = translator.translate(tree)

        logger.debug(s"Taking Viper preamble from resources/${VoilaConstants.preambleFile}")

        FileUtils.copyFile(preambleFile, outputFile)

        logger.debug(s"Writing generated program to file ${config.outputFile()}")

        FileUtils.writeStringToFile(
          outputFile,
          silver.ast.pretty.FastPrettyPrinter.pretty(viperProgram),
          UTF_8,
          true)

//        tree.nodes foreach (n => {
//          frontend.positions.getStart(n) match {
//            case Some(x) =>
//            case None => println(s"  NO POSITION FOR $n")
//          }
//        })

        logger.info("Encoded Voila program in Viper")
        logger.info("Verifying encoding using Silicon ...")
        val silicon = new Silicon
        silicon.start()
        val verificationResult = silicon.handle(viperProgram)
        silicon.stop()
        logger.info(s"... done (with ${getNumberOfErrors(verificationResult)} Viper error(s))")

        verificationResult match {
          case silver.verifier.Success => /* Nothing left to do */
          case failure: silver.verifier.Failure =>
            extractVerificationFailures(failure) match {
              case (Seq(), viperErrors) =>
                /* No verification failures, but, e.g. type-checking failures */
                logger.error("Found non-verification-failures:")
                viperErrors foreach (ve => logger.error(ve.readableMessage))
              case (viperErrors, Seq()) =>
                /* Only verification failures */
                logger.error(s"Voila found potential errors:")
                viperErrors foreach (viperError =>
                  errorBacktranslator.translate(viperError) match {
                    case None =>
                      /* Back-translation didn't work */
                      logger.error(s"  ${viperError.readableMessage}")
                    case Some(voilaError) =>
                      logger.error(s"  ${voilaError.message(frontend.positions)}")
                  })
            }
        }
    }
  }
}

object Voila extends StrictLogging {
  def main(args: Array[String]) {
    val config = new Config(args)

    setLogLevelsFromConfig(config)

    val inputFile = new File(config.inputFile())
    val outputFile = new File(config.outputFile())

    val preambleFile = {
      val resource = getClass.getResource(VoilaConstants.preambleFile)

      if (resource == null)
        exitWithError(s"Cannot access resource ${VoilaConstants.preambleFile}")

      new File(resource.getFile)
    }

    logger.info(VoilaConstants.versionMessage)

    if (!inputFile.isFile) exitWithError(s"${config.inputFile()} is not a file")
    if (!inputFile.canRead) exitWithError(s"Cannot read from ${config.inputFile()}")
    if (!preambleFile.isFile) exitWithError(s"$preambleFile is not a file")
    if (!preambleFile.canRead) exitWithError(s"Cannot read from $preambleFile")

    logger.debug(s"Reading source program from file ${config.inputFile()}")

    val frontend = new Frontend()

    frontend.parse(FileUtils.readFileToString(inputFile, UTF_8)) match {
      case Left(messages) =>
        frontend.reportErrors(
          s"Parsing ${config.inputFile()} failed with ${messages.length} error(s):",
          messages)

        sys.exit(1)

      case Right(program) =>
        /* TODO: Move semantic analysis to the frontend */

        logger.info("Parsed")
        logger.info(s"  ${program.regions.length} region(s): ${program.regions.map(_.id.name).mkString(", ")}")
        logger.info(s"  ${program.predicates.length} predicate(s): ${program.predicates.map(_.id.name).mkString(", ")}")
        logger.info(s"  ${program.procedures.length} procedures(s): ${program.procedures.map(_.id.name).mkString(", ")}")

        val tree = new VoilaTree(program)
        val semanticAnalyser = new SemanticAnalyser(tree)
        val messages = semanticAnalyser.errors

        if (messages.nonEmpty) {
          frontend.reportErrors(
            s"Type-checking ${config.inputFile()} failed with ${messages.length} error(s):",
            messages)

          sys.exit(1)
        }

        val translator = new PProgramToViperTranslator(semanticAnalyser)
        val (viperProgram, errorBacktranslator) = translator.translate(tree)

        logger.debug(s"Taking Viper preamble from resources/${VoilaConstants.preambleFile}")

        FileUtils.copyFile(preambleFile, outputFile)

        logger.debug(s"Writing generated program to file ${config.outputFile()}")

        FileUtils.writeStringToFile(
          outputFile,
          silver.ast.pretty.FastPrettyPrinter.pretty(viperProgram),
          UTF_8,
          true)

//        tree.nodes foreach (n => {
//          frontend.positions.getStart(n) match {
//            case Some(x) =>
//            case None => println(s"  NO POSITION FOR $n")
//          }
//        })

        logger.info("Encoded Voila program in Viper")
        logger.info("Verifying encoding using Silicon ...")
        val silicon = new Silicon
        silicon.start()
        val verificationResult = silicon.handle(viperProgram)
        silicon.stop()
        logger.info(s"... done (with ${getNumberOfErrors(verificationResult)} Viper error(s))")

        verificationResult match {
          case silver.verifier.Success => /* Nothing left to do */
          case failure: silver.verifier.Failure =>
            extractVerificationFailures(failure) match {
              case (Seq(), viperErrors) =>
                /* No verification failures, but, e.g. type-checking failures */
                logger.error("Found non-verification-failures:")
                viperErrors foreach (ve => logger.error(ve.readableMessage))
              case (viperErrors, Seq()) =>
                /* Only verification failures */
                logger.error(s"Voila found potential errors:")
                viperErrors foreach (viperError =>
                  errorBacktranslator.translate(viperError) match {
                    case None =>
                      /* Back-translation didn't work */
                      logger.error(s"  ${viperError.readableMessage}")
                    case Some(voilaError) =>
                      logger.error(s"  ${voilaError.message(frontend.positions)}")
                  })
            }
        }
    }

    logger.info("Voila finished")
    sys.exit(0)
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

  def exitWithError(message: String, exitCode: Int = 1): Unit = {
    logger.error(message)

    sys.exit(exitCode)
  }

  private def setLogLevelsFromConfig(config: Config) {
    val logger = LoggerFactory.getLogger(this.getClass.getPackage.getName).asInstanceOf[Logger]
    logger.setLevel(Level.toLevel(config.logLevel()))
  }
}
