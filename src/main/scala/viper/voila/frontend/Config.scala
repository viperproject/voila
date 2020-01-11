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

  val enableStabilityChecks: ScallopOption[Boolean] = opt[Boolean](
    name = "enableStabilityChecks",
    descr = "Enables stability checks of pre-/postconditions, region interpretations and invariants",
    default = Some(true),
    noshort = true)

  val enableTransitivityChecks: ScallopOption[Boolean] = opt[Boolean](
    name = "enableTransitivityChecks",
    descr = "Enables transitivity checks of actions",
    default = Some(true),
    noshort = true)

  val disableSiliconSpecificHavockingCode: ScallopOption[Boolean] = opt[Boolean](
    name = "disableSiliconSpecificHavockingCode",
    descr =
      "By default, Voila generates special Viper code that allows Silicon to efficiently havoc resources, which " +
          "can tremendously improve Voila's performance. See also Silicon option --disableHavocHack407 and the " +
          "corresponding Silicon issue #407.",
    default = Some(false),
    noshort = true)

  val useForpermsInsteadOfQPs: ScallopOption[Boolean] = opt[Boolean](
    name = "useForpermsInsteadOfQPs",
    descr = "Experimental: potentially faster, but less complete.",
    default = Some(true),
    noshort = true)

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
