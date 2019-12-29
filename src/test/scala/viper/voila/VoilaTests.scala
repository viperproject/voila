/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import java.nio.file.{Path, Paths}

import org.scalatest.BeforeAndAfterAll
import viper.voila.frontend.Config
import viper.voila.reporting.{Failure, Success, VoilaError}
import viper.silver.testing._
import viper.silver.utility.TimingUtils

class VoilaTests extends AnnotationBasedTestSuite with BeforeAndAfterAll {
  val testDirectories: Vector[String] = Vector("regressions", "examples")
  override val defaultTestPattern: String = ".*\\.vl"

  var voilaInstance: Voila = _

  override def beforeAll(): Unit = {
    voilaInstance = new Voila()
  }

  override def afterAll(): Unit = {
    voilaInstance = null
  }

  val voilaInstanceUnderTest: VoilaUnderTest = new VoilaUnderTest()

  def systemsUnderTest: Vector[SystemUnderTest] = Vector(voilaInstanceUnderTest)

  protected class VoilaUnderTest extends SystemUnderTest with TimingUtils {
    val projectInfo: ProjectInfo = new ProjectInfo(List("Voila"))
    val reportRuntime: Boolean = true

    protected def adjustCommandLineOptions(options: Vector[CommandLineArgument]): Vector[CommandLineArgument] =
      options

    def run(testInput: AnnotatedTestInput): Vector[AbstractOutput] = {
      var voilaConfigOptions: Vector[CommandLineArgument] =
        Vector(
          OptionArgument("--logLevel", "ERROR"),
          OptionArgument("-i", testInput.file.toFile.getPath))

      configMap.get("saveViperFilesIn").foreach(viperFileDirectory => {
        val viperOutputFilepath =
          Paths.get(viperFileDirectory.toString, testInput.prefix, s"${testInput.file.toFile.getName}.vpr")

        voilaConfigOptions :+= OptionArgument("-o", viperOutputFilepath.toFile.getPath)
      })

      voilaConfigOptions = adjustCommandLineOptions(voilaConfigOptions)
      val config = new Config(voilaConfigOptions.flatMap(_.asSeq))

      val (result, elapsed) = time(() => voilaInstance.verify(config))

      if (reportRuntime) info(s"Time required: $elapsed")

      result match {
        case None =>
          info("Voila failed")
          Vector.empty
        case Some(Success) =>
          Vector.empty
        case Some(Failure(errors)) =>
          errors map VoilaTestOutput
      }
    }
  }
}


case class VoilaTestOutput(error: VoilaError) extends AbstractOutput {
  // TODO: Computing lazy val before Kiama position information is deallocated shouldn't be
  //       necessary, but currently is.
  error.position

  def isSameLine(file: Path, lineNr: Int): Boolean = error.position.line == lineNr
  def fullId: String = error.id
}


sealed trait CommandLineArgument {
  def asSeq: Seq[String]
}

final case class OptionArgument(key: String, value: String) extends CommandLineArgument {
  val asSeq: Seq[String] = Vector(key, value)
}

final case class FlagArgument(key: String) extends CommandLineArgument {
  val asSeq: Seq[String] = Vector(key)
}
