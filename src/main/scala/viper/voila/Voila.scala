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
import org.slf4j.LoggerFactory
import viper.voila.frontend.{Config, Frontend, SemanticAnalyser, VoilaTree}
import viper.silver.ast.pretty.FastPrettyPrinter

object VoilaConstants {
  val toolName = "Voila"
  val toolVersion = "0.1"
  val toolCopyright = "(c) Copyright ETH Zurich 2016"

  val versionMessage = s"${VoilaConstants.toolName} ${VoilaConstants.toolVersion} ${VoilaConstants.toolCopyright}"
}

object Voila extends StrictLogging {
  def main(args: Array[String]) {
    val config = new Config(args)

    setLogLevelsFromConfig(config)

    val inputFile = new File(config.inputFile())
    val outputFile = new File(config.outputFile())

    logger.info(VoilaConstants.versionMessage)

    if (!inputFile.isFile) exitWithError(s"${config.inputFile()} is not a file")
    if (!inputFile.canRead) exitWithError(s"Cannot read from ${config.inputFile()}")

    logger.debug(s"Reading source program from file ${config.inputFile()}")

    val frontend = new Frontend()

    frontend.parse(FileUtils.readFileToString(inputFile, UTF_8)) match {
      case Left(messages) =>
        frontend.reportErrors(
          s"Parsing ${config.inputFile()} failed with ${messages.length} error(s):",
          messages)
        //      logger.error(s"Parsing ${config.inputFile()} failed with ${messages.length} error(s):")
        //      messages foreach (m => logger.error(s"  $m"))
        sys.exit(1)

      case Right(program) =>
        /* TODO: Move semantic analysis to the frontend */

        val tree = new VoilaTree(program)
        val semanticAnalyser = new SemanticAnalyser(tree)
        val messages = semanticAnalyser.errors

        if (messages.nonEmpty) {
          frontend.reportErrors(
            s"Type-checking ${config.inputFile()} failed with ${messages.length} error(s):",
            messages)
          //        if (logger.underlying.isErrorEnabled) {
          //          messages.sorted(frontend.messageOrdering)
          //                  .foreach(m => logger.error(frontend.formatMessage(m)))
          //        }
          sys.exit(1)
        }

        val translator = new PProgramToViperTranslator(semanticAnalyser)
        val viperProgram = translator.translate(tree)

        logger.debug(s"Writing generated program to file ${config.outputFile()}")

        FileUtils.writeStringToFile(
          outputFile,
          FastPrettyPrinter.pretty(viperProgram),
          UTF_8)
    }

    logger.info("Done")
    sys.exit(0)
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
