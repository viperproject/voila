/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import java.io.File
import java.nio.charset.StandardCharsets.UTF_8
import scala.util.{Left, Right}
import com.typesafe.scalalogging.StrictLogging
import org.apache.commons.io.FileUtils
import viper.voila.frontend.{Config, Frontend}
import viper.silver.ast.pretty.FastPrettyPrinter

object VoilaConstants {
  val toolName = "Voila"
  val toolVersion = "0.1"
  val toolCopyright = "(c) Copyright ETH Zurich 2016"

  val versionMessage = s"${VoilaConstants.toolName} ${VoilaConstants.toolVersion} ${VoilaConstants.toolCopyright}"
}

object Voila extends App with StrictLogging {
  val config = new Config(args, logger)

  val inputFile = new File(config.inputFile())
  val outputFile = new File(config.outputFile())

  logger.info(VoilaConstants.versionMessage)
  logger.debug(s"Reading source program from file ${config.inputFile()}")

  val frontend = new Frontend()

  frontend.parse(FileUtils.readFileToString(inputFile, UTF_8)) match {
    case Left(messages) =>
      logger.error(s"Parsing ${config.inputFile()} failed with ${messages.length} error(s):")
      messages foreach (m => logger.error(s"  $m"))
      sys.exit(1)

    case Right(voilaProgram) =>
      val translator = new PProgramToViperTranslator()
      val viperProgram = translator.translate(voilaProgram)

      logger.debug(s"Writing generated program to file ${config.outputFile()}")

      FileUtils.writeStringToFile(
        outputFile,
        FastPrettyPrinter.pretty(viperProgram),
        UTF_8)
  }

  logger.info("Done")
  sys.exit(0)
}
