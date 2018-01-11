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

  version(VoilaConstants.versionMessage)

  banner(s"""Usage: ${VoilaConstants.toolName} [OPTIONS] -i <input-file>
            |
            |Options:
            |""".stripMargin)

  /*
   * Command-line options
   */

  val inputFile: ScallopOption[String] = opt[String](
    name = "inputFile",
    descr = "Voila program to verify is read from this file",
    required = true)

  val outputFile: ScallopOption[String] = opt[String](
    name = "outputFile",
    descr = "Generated Viper program is written to this file")

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

  /*
   * Exception handling
   */

  override def onError(e: Throwable): Unit = {
    e match {
      case exceptions.Version =>
        logger.info(builder.vers.get)
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
