/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import com.typesafe.scalalogging.Logger
import org.rogach.scallop.{Scallop, ScallopConf, ScallopOption, exceptions}
import viper.voila.VoilaConstants

class Config(arguments: Seq[String], logger: Logger) extends ScallopConf(arguments) {
  version(VoilaConstants.versionMessage)

  banner(s"""Usage: ${VoilaConstants.toolName} [OPTION]
           |
           |Options:
           |""".stripMargin)

  val inputFile: ScallopOption[String] = opt[String](
    name = "inputFile",
    descr = "Voila program to verify is read from this file",
    required = true)

  val outputFile: ScallopOption[String] = opt[String](
    name = "outputFile",
    descr = "Generated Viper program is written to this file",
    required = true)

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

  verify()
}