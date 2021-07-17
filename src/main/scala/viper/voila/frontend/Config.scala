/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import com.typesafe.scalalogging.StrictLogging
import org.rogach.scallop.{Scallop, ScallopConf, ScallopOption, exceptions, singleArgConverter}
import viper.voila.VoilaConstants

class Config(arguments: Seq[String])
  extends ScallopConf(arguments)
    with StrictLogging {

  /* Attention: Don't use options to compute default values! This will cause
   * a crash when help is printed (--help) because of the order in which things
   * are initialised.
   */

  /*
   * Prologue
   */

  version(VoilaConstants.toolNameAndVersion)

  banner(s"""Usage: ${VoilaConstants.toolName} [OPTIONS] -i <input-file>
            |
            |Options:
            |""".stripMargin)

  /*
   * Command-line options
   */

  val inputFileName: ScallopOption[String] = opt[String](
    name = "input",
    descr = "Voila program to verify is read from this file",
    required = true)

  val outputFileName: ScallopOption[String] = opt[String](
    name = "output",
    descr = "Generated Viper program is written to this file")

  val outputParsedProgramFileName: ScallopOption[String] = opt[String](
    name = "outputParsedProgram",
    descr = "Writes the parsed and desugared Voila program back to this file",
    default = None,
    noshort = true)

  val logLevel: ScallopOption[String] = opt[String](
    name = "logLevel",
    descr = "One of the log levels ALL, TRACE, DEBUG, INFO, WARN, ERROR, OFF (default: OFF)",
    default = Some("INFO"),
    noshort = true
  )(singleArgConverter(level => level.toUpperCase))

  val include: ScallopOption[List[String]] = opt[List[String]](
    name = "include",
    descr = "A space-separated list of procedures to verify",
    noshort = true)

  val disableStabilityChecks: ScallopOption[Boolean] = opt[Boolean](
    name = "disableStabilityChecks",
    descr = "Enables stability checks of pre-/postconditions, region interpretations and invariants",
    default = Some(false),
    noshort = true)

  val disableTransitivityChecks: ScallopOption[Boolean] = opt[Boolean](
    name = "disableTransitivityChecks",
    descr = "Enables transitivity checks of actions",
    default = Some(false),
    noshort = true)

  val disableSiliconSpecificHavockingCode: ScallopOption[Boolean] = opt[Boolean](
    name = "disableSiliconSpecificHavockingCode",
    descr =
      "By default, Voila generates special Viper code that allows Silicon to efficiently havoc resources, which " +
        "can tremendously improve Voila's performance. See also Silicon option --disableHavocHack407 and the " +
        "corresponding Silicon issue #407.",
    default = Some(false),
    noshort = true)

  val useQPsInsteadOfForperms: ScallopOption[Boolean] = opt[Boolean](
    name = "useQPsInsteadOfForperms",
    descr = "Using Viper's quantified permissions instead of forperm expressions is slower, but more complete.",
    default = Some(false),
    noshort = true)

//  val useCarbon: ScallopOption[Boolean] = opt[Boolean](
//    name = "useCarbon",
//    descr = "By default, Voila uses Silicon as the backend. Set this flag to use Carbon instead.",
//    default = Some(false),
//    noshort = true)
//
//  validateOpt(useCarbon, disableSiliconSpecificHavockingCode, useQPsInsteadOfForperms) {
//    case (Some(true), Some(false), _) => sys.error("If Carbon is used, the " + s"--${disableSiliconSpecificHavockingCode.name}"
//      + " option must be set, otherwise the Viper encoding is not correct.")
//    case  (Some(true), Some(true), Some(false)) => sys.error(s"If Carbon is used, the " + s"--${useQPsInsteadOfForperms.name}"
//      + " must be set, because Carbon does not support generalized forperm expressions.")
//    case _ => Right(())
//  }

  /*
   * Exception handling
   */

  override def onError(e: Throwable): Unit = {
    e match {
      case exceptions.Version =>
        logger.info(builder.vers.get)
        sys.exit(0)
      case exceptions.Help("") =>
        printHelp(builder)
        sys.exit(0)
      case exceptions.Help(subname) =>
        printHelp(builder.findSubbuilder(subname).get)
        sys.exit(0)
      case exceptions.ScallopException(message) =>
        logger.info(builder.vers.get)
        logger.info("")
        logger.error(s"Command-line error: $message")
        logger.info("")
        logger.info(builder.bann.get)
        logger.info(builder.help)
        sys.exit(1)
    }
  }

  protected def printHelp(forBuilder: Scallop): Unit = {
    logger.info(forBuilder.vers.get)
    logger.info(forBuilder.bann.get)
    logger.info(forBuilder.help)
  }

  /*
   * Epilogue
   */

  /* Immediately finalise command-line parsing */
  verify()
}
