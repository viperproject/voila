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
import viper.voila.backends.{MockViperFrontend, Silicon, Carbon, ViperVerifier, ViperNameSanitizer, ViperPreamble}
import viper.voila.frontend._
import viper.voila.reporting._
import viper.voila.translator.{ErrorBacktranslator, PProgramToViperTranslator}

object VoilaConstants {
  val toolName: String  = "Voila"
  val toolCopyright: String  = "(c) Copyright ETH Zurich 2016 - 2019"

  val buildRevision = BuildInfo.gitRevision
  val buildBranch = BuildInfo.gitBranch

  val buildVersion: Option[String] =
    if (buildRevision.isEmpty && buildBranch.isEmpty) None
    else if (buildBranch == "master") Some(buildRevision)
    else Some(s"$buildRevision@$buildBranch")

  val toolVersion: String =
    s"${BuildInfo.projectVersion}${buildVersion.fold("")(v => s" ($v)")}"

  val toolNameAndVersion: String = s"$toolName $toolVersion"

  val preambleFile: String  = "preamble.vpr"
}

object VoilaErrorCodes {
  val DEFAULT = 1
  val POSITION_PROBLEMS = 10
  val OPTION_PROBLEMS = 20
}

// TODO: Remove global state
object VoilaGlobalState {
  var config: Config = _
  var positions: Positions = _
}

class Voila extends StrictLogging {
  // TODO: Have verify() return VerificationDurationRecord instead of storing it here.
  //       Maybe include in the returned VoilaResult.
  var _lastDurations: Option[VerificationDurationRecord] = None

  def lastDuration: Option[VerificationDurationRecord] = _lastDurations

  def lastDuration_=(duration: VerificationDurationRecord): Unit = {
    _lastDurations = Some(duration)
  }


  val defaultPreambleFile: Path = {
    val resource = getClass.getClassLoader.getResource(VoilaConstants.preambleFile)

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

  def verify(file: Path, originalConfig: Config): Option[VoilaResult] = {
    var config = originalConfig

    VoilaGlobalState.config = config // TODO: Remove global state
    setLogLevelsFromConfig(config)

    /* TODO: Code further down alternates between use of `file` and `config.inputFileName`.
     *       If both values are expected to be equal, why pass `file` at all?
     */

    logger.info(VoilaConstants.toolNameAndVersion)

    if (!Files.isRegularFile(file)) exitWithError(s"${config.inputFileName()} is not a file")
    if (!Files.isReadable(file)) exitWithError(s"Cannot read from ${config.inputFileName()}")

    logger.debug(s"Reading source program from file ${config.inputFileName()}")

    val frontend = new Frontend()

    VoilaGlobalState.positions = frontend.positions // TODO: Remove global state

    var timer: Timer = null
    val durations = new VerificationDurationRecord()
    lastDuration = durations


    // Step 1: Parsing
    timer = TimingUtils.startTimer()

    val parserResult = frontend.parse(file)

    timer.stop()
    durations.parsing = Some(timer.durationMillis)


    parserResult match {
      case Left(voilaErrors) =>
        Some(Failure(voilaErrors))

      case Right(program) =>
        /* TODO: Move semantic analysis to the frontend */

        abortIfConfigOptionToolUnknown(program.options)
        config = setVoilaConfigOptions(program.options, config.args)
        setLogLevelsFromConfig(config)
        VoilaGlobalState.config = config // TODO: Remove global state

        logger.info("Parsed")
        logger.info(s"  ${program.regions.length} region(s): ${program.regions.map(_.id.name).mkString(", ")}")
        logger.info(s"  ${program.predicates.length} predicate(s): ${program.predicates.map(_.id.name).mkString(", ")}")
        logger.info(s"  ${program.procedures.length} procedures(s): ${program.procedures.map(_.id.name).mkString(", ")}")

        potentiallyPrettyPrintParsedProgramToFile(config, program)
        potentiallyReportExcludedProcedures(config, program)


        // Step 2: Typechecking
        timer.start()

        val tree = new VoilaTree(program)

        abortIfTreeHasPositionProblems(tree, frontend.positions)

        val semanticAnalyser = new SemanticAnalyser(tree)

        timer.stop()
        durations.typechecking = Some(timer.durationMillis)


        val messages = semanticAnalyser.errors

        if (messages.nonEmpty) {
          val voilaErrors = frontend.translateToVoilaErrors(messages, TypecheckerError)

          return Some(Failure(voilaErrors))
        }

        val nameSanitizer = new ViperNameSanitizer()

        logger.debug(s"Taking Viper preamble from ${defaultPreambleFile.toString}")


        // Step 3: Translating
        timer.start()

        val preambleProgram =
          defaultPreamble match {
            case None =>
              val msg = s"Could not parse Viper preamble ${defaultPreambleFile.toString}"

              return Some(Failure(Vector(ResourceError(msg))))

            case Some(_preambleProgram) =>
              _preambleProgram
          }

        val preamble = new ViperPreamble(preambleProgram)

        val translator =
          new PProgramToViperTranslator(config, semanticAnalyser, preamble, nameSanitizer)

        val (translatedProgram, errorBacktranslator) = translator.translate(tree)

        val programToVerify =
          translatedProgram.copy(
            domains = preambleProgram.domains ++ preamble.generatedDomains ++ translatedProgram.domains,
            fields = preambleProgram.fields ++ translatedProgram.fields,
            functions = preambleProgram.functions ++ translatedProgram.functions,
            predicates = preambleProgram.predicates ++ translatedProgram.predicates,
            methods = preambleProgram.methods ++ translatedProgram.methods
          )(translatedProgram.pos, translatedProgram.info, translatedProgram.errT)

        timer.stop()
        durations.translation = Some(timer.durationMillis)


        potentiallyPrettyPrintViperProgramToFile(config, programToVerify)


        // Step 4: Checking consistency
        timer.start()

        var consistencyCheckResults = programToVerify.checkTransitively

        timer.stop()
        durations.consistency = Some(timer.durationMillis)

        if (!config.useQPsInsteadOfForperms()) {
          consistencyCheckResults =
            consistencyCheckResults.filterNot(
              _.message.startsWith("Body of forperm quantifier is not allowed to contain perm expressions"))
        }

        consistencyCheckResults match {
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

        // Step 5: Verification
        var backend: ViperVerifier = null
        if(!config.useCarbon()) {
          var siliconOptions: Vector[String] = Vector.empty
          //        siliconOptions ++= Vector("--numberOfParallelVerifiers", "1")
          siliconOptions ++= Vector("--logLevel", "ERROR")
          siliconOptions ++= Vector("--disableCatchingExceptions")
          siliconOptions ++= Vector("--disableMostStateConsolidations")

          if (config.disableSiliconSpecificHavockingCode()) {
            // Disabling Silicon's support for this hack isn't strictly necessary, but can't hurt, either
            siliconOptions ++= Vector("--disableHavocHack407")
          }

          logger.info("Encoded Voila program in Viper")

          timer.start()

          logger.info("Verifying encoding using Silicon ...")
          backend = new Silicon(siliconOptions)
        } else {
          logger.info("Encoded Voila program in Viper")

          timer.start()

          logger.info("Verifying encoding using Carbon ...")
          backend = new Carbon(Vector.empty, config)
        }

        backend.start()
        val verificationResult = backend.handle(programToVerify)
        backend.stop()

        timer.stop()
        durations.verification = Some(timer.durationMillis)


        logger.info(s"... done (with ${getNumberOfErrors(verificationResult)} Viper error(s))")

        backtranslateOrReportErrors(verificationResult, errorBacktranslator)
    }
  }

  private def abortIfConfigOptionToolUnknown(configOptions: Vector[PConfigOption]): Unit = {
    var abort = false

    configOptions foreach (configOption => {
      if (!Set("voila", "silicon", "carbon").contains(configOption.tool)) {
        abort = true
        logger.error(s"### UNRECOGNISED TOOL '${configOption.tool}' IN '$configOption'")
      }
    })

    if (abort) exitWithError("Config option problems!", VoilaErrorCodes.OPTION_PROBLEMS)
  }

  private def setVoilaConfigOptions(configOptions: Vector[PConfigOption], originalArguments: Seq[String]): Config = {
    assert(configOptions.forall(_.tool == "voila"), s"Expected only options for Voila, but got: $configOptions")

    // The argument filter to come makes the following assumptions:
    // 1) Each configOption's option denotes the homonymous command line option, prefixed with "--".
    //    E.g. a configOption "foo" denotes the command line option "--foo".
    // 2) A configOption's option matches an originalArgument if the latter is the former, prefixed with "--".
    //    E.g. "foo" matches "--foo", but not "foo", "-foo" or "barfoo".
    //    This is a best-effort attempt at differentiating between option names and values in the originalArguments
    //    string sequence.
    // 3) If a configOption's value is Some(value) and a matching originalArgument option is found, then the next
    //    string in the originalArgument sequence is the original value.
    //    E.g. given a configOption with option == "foo" and value == "bar", and an originalArguments sequence
    //    [..., "--foo", "qux", ...], then the original value must have been "qux". This assumption might not hold if
    //    an option's value is optional.
    //
    // The code is not optimised for efficiency, but that's most likely not necessary.

    val originalArgumentsWithIndices = originalArguments.zipWithIndex

    val acceptedConfigOptions =
      configOptions.filter(configOption => {
        val matchingOriginalArgumentWithIndex =
          originalArgumentsWithIndices.find { case(arg, _) => arg.drop(2) == configOption.option }

        matchingOriginalArgumentWithIndex
          .foreach { case (originalArgument, originalIndex) =>
            val original =
              if (configOption.value.isEmpty) {
                s"$originalArgument"
              } else {
                val originalValue = originalArguments(originalIndex + 1)
                s"$originalArgument $originalValue"
              }

            logger.warn(s"'$configOption' will be ignored because '$original' was explicitly provided")
          }

        matchingOriginalArgumentWithIndex.isEmpty
      })

    val acceptedArguments =
      acceptedConfigOptions.flatMap(configOption => s"--${configOption.option}" +: configOption.value.toSeq)

    logger.info(s"Accepted additional options: ${acceptedArguments.mkString(" ")}")

    new Config(originalArguments ++ acceptedArguments)
  }

  /* Pretty-print the parsed and desugared Voila program back to a file, if requested. */
  private def potentiallyPrettyPrintParsedProgramToFile(config: Config, program: PProgram): Unit = {
    config.outputParsedProgramFileName.map(new File(_)).foreach(outputFile => {
      logger.info(
        "Writing parsed and desugared input program back to file " +
          s"${config.outputParsedProgramFileName()}")

      FileUtils.writeStringToFile(outputFile, program.pretty, UTF_8)
    })
  }

  private def potentiallyReportExcludedProcedures(config: Config, program: PProgram): Unit = {
    if (config.include.supplied) {
      val excludedProcedures: Vector[String] =
        program.procedures
          .map(_.id.name)
          .filterNot(config.include().contains)

      if (excludedProcedures.nonEmpty) {
        logger.warn(
          "The following procedures will be excluded from verification: " +
            excludedProcedures.mkString(", "))
      }
    }
  }

  private def abortIfTreeHasPositionProblems(tree: VoilaTree, positions: Positions): Unit = {
    var abort = false

    tree.nodes foreach (n => {
      positions.getStart(n) match {
        case Some(_) => /* OK, nothing to do */
        case None =>
          abort = true
          logger.error(s"### NO POSITION FOR ${n.getClass.getSimpleName}:\n  $n")
      }
    })

    if (abort) exitWithError("Position problems!", VoilaErrorCodes.POSITION_PROBLEMS)
  }

  /* Pretty-print the generated Viper program to a file, if requested. */
  private def potentiallyPrettyPrintViperProgramToFile(config: Config, programToVerify: silver.ast.Program): Unit = {
    config.outputFileName.map(new File(_)).foreach(outputFile => {
      logger.debug(s"Writing generated program to file ${config.outputFileName()}")

      FileUtils.writeStringToFile(
        outputFile,
        silver.ast.pretty.FastPrettyPrinter.pretty(programToVerify),
        UTF_8)
    })
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


  def exitWithError(message: String, exitCode: Int = VoilaErrorCodes.DEFAULT): Unit = {
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
