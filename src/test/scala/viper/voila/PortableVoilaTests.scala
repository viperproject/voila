// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.voila

import java.io.{BufferedWriter, File, FileWriter}
import java.nio.file.{Path, Paths => JPaths}

import org.scalatest.{BeforeAndAfterEach, DoNotDiscover}
import viper.silver.testing.{AbstractOutput, AnnotatedTestInput}
import viper.silver.utility.Paths
import viper.voila.reporting.{TimingUtils, VerificationDurationRecord}


/** See [[viper.silicon.tests.PortableSiliconTests()]] for details.
  *
  * TODO: Currently can't extend [[viper.silver.testing.StatisticalTestSuite]] because it expects
  *       that the frontend (here: Voila) extends certain traits (e.g. Verifier, Frontend, ...) that
  *       declare abstract methods that Voila cannot implement implement in reasonable ways.
  */
@DoNotDiscover
class PortableVoilaTests extends VoilaTests with BeforeAndAfterEach {
  protected val repetitionsPropertyName = "VOILATESTS_REPETITIONS"
  protected val targetLocationPropertyName = "VOILATESTS_TARGET"
  protected val csvFilePropertyName = "VOILATESTS_CSV"
  protected val voilaOptionsPropertyName = "VOILATESTS_VLOPTS"

  private var csvFile: BufferedWriter = _

  protected val targetDirName: String =
    Option(System.getProperty(targetLocationPropertyName)) match {
      case Some(name) => name
      case None => fail(s"Property '$targetLocationPropertyName' not set")
    }

  override val testDirectories: Vector[String] = Vector(targetDirName)

  override val voilaInstanceUnderTest: VoilaUnderTest = new VoilaUnderPortableTest()

  protected class VoilaUnderPortableTest extends VoilaUnderTest {
    private var lastCommandLineOptions: Vector[CommandLineArgument] = _

    override val reportRuntime: Boolean = false

    override protected def adjustCommandLineOptions(options: Vector[CommandLineArgument]): Vector[CommandLineArgument] = {
      var adjustedOptions = super.adjustCommandLineOptions(options)

      // TODO: Passing additional arguments this way could be supported by VoilaTests.scala directly

      val voilaOptionsPropertyValue =
        Option(System.getProperty(voilaOptionsPropertyName)).fold("")(_.trim)

      if (voilaOptionsPropertyValue.trim.nonEmpty) {
        // The value of property <voilaOptionsPropertyName> is expected to be a comma-separated
        // list of Voila command-line arguments, with key-value options in the format "key=value".
        //
        // Example:
        //   -D<voilaOptionsPropertyName> --enableStabilityChecks,--logLevel=ALL,--enableTransitivityChecks
        //
        // TODO: Most likely won't work in all situations. E.g. to investigate: could it happen
        //       that a Voila argument contains an equals sign? What about quotes?

        val additionalOptions: Array[CommandLineArgument] =
          for (option <- voilaOptionsPropertyValue.split(',')) yield {
            if (option.contains('=')) {
              val Array(key, value) = option.split('=')

              OptionArgument(key, value)
            } else {
              FlagArgument(option)
            }
          }

        adjustedOptions ++= additionalOptions
      }

      lastCommandLineOptions = adjustedOptions

      adjustedOptions
    }

    override def run(testInput: AnnotatedTestInput): Vector[AbstractOutput] = {
      val data: IndexedSeq[TestRunData] =
        for (_ <- 1 to repetitions) yield {
          val (outputs, totalRuntime) =
            TimingUtils.time(() => super.run(testInput))

          report(s"Voila arguments: ${lastCommandLineOptions.flatMap(_.asSeq).mkString(" ")}")
          report(s"Total test runtime: $totalRuntime")

          TestRunData(outputs, voilaInstance.lastDuration.get, totalRuntime)
        }

      if (1 < data.length) {
        Predef.assert(
          data.tail.forall(_.outputs == data.head.outputs),
          s"Did not get the same errors for all repetitions: ${data.map(_.outputs)}")
      }

      reportTestRunData(testInput, data)

      data.head.outputs
    }
  }

  /** It is expected that each run yielded the same verification results, i.e. that all fields
    * data.outputs are equal.
    */
  protected def reportTestRunData(testInput: AnnotatedTestInput, data: Seq[TestRunData]): Unit = {
    val sortedData = data.sortBy(_.totalRuntime)

    // TODO: The remaining code has been copy-adopted from StatisticalTestSuite.
    //       Copying should not be necessary.

    val trimmedData =
      if (3 <= sortedData.length) {
        report(s"Dropped best and worst test repetition runtime (i.e. 2/${sortedData.length}.")

        // Drop first and last
        sortedData.tail.init
      } else {
        sortedData
      }

    // A row = runtime per phase, for one test run.
    // A column = runtime per test run, for one phase.
    // Table layout thus:
    //     p1  p2  p3  ...
    // r1  t11 t21 t31 ...
    // r2  t12 t22 t32 ...
    // r2  t14 t24 t34 ...
    // ...
    val durationPerPhaseTable: Seq[Seq[Long]] =
      trimmedData.map(_.durationRecord.asValuesRow)

    val meanTimePerPhase: Seq[Long] =
      durationPerPhaseTable
        .transpose
         // Each col is a column from meanTimingPerPhase
        .map(col => (col.sum.toFloat / col.length).toLong)

    val bestTimePerPhase: Seq[Long] = durationPerPhaseTable.head
    val medianTimePerPhase: Seq[Long] = durationPerPhaseTable(durationPerPhaseTable.length / 2)
    val worstTimePerPhase: Seq[Long] = durationPerPhaseTable.last

    val stddevTimings: Seq[Long] =
      durationPerPhaseTable
        .transpose
        .zip(meanTimePerPhase)
        .map { case (col, mean) =>
          math.sqrt(col.map(v => math.pow(v - mean, 2)).sum / col.length).toLong
        }

    val relStddevTimings: Seq[Long] =
      stddevTimings
        .zip(meanTimePerPhase)
        .map { case (stddev, mean) =>
          (100.0 * stddev / math.abs(mean)).toLong
        }

    val phaseNames = data.head.durationRecord.propertyNames

    if (repetitions == 1) {
      report(s"Time per phase: ${printableTimings(meanTimePerPhase, phaseNames)}.")
    } else {
      val n = "%2d".format(durationPerPhaseTable.length)

      report(s"Mean / $n runs: ${printableTimings(meanTimePerPhase, phaseNames)}.")
      report(s"Stddevs:        ${printableTimings(stddevTimings, phaseNames)}.")
      report(s"Rel. stddev:    ${printablePercentage(relStddevTimings, phaseNames)}.")
      report(s"Best run:       ${printableTimings(bestTimePerPhase, phaseNames)}.")
      report(s"Median run:     ${printableTimings(medianTimePerPhase, phaseNames)}.")
      report(s"Worst run:      ${printableTimings(worstTimePerPhase, phaseNames)}.")

      if (csvFileName.isDefined) {
        val csvRowData = Seq(
          JPaths.get(targetDirName).toAbsolutePath.relativize(testInput.file.toAbsolutePath),
          data.head.outputs.length,
          meanTimePerPhase.last, stddevTimings.last, relStddevTimings.last,
          bestTimePerPhase.last, medianTimePerPhase.last, worstTimePerPhase.last)

        csvFile.write(csvRowData.mkString(","))
        csvFile.newLine()
        csvFile.flush()
      }
    }
  }

  private def report(string: String): Unit =
    super.info(s"[Voila benchmark] $string")

  // TODO: The next few methods have been copy-adopted from the StatisticalTestSuite.
  //       Copying them should not be necessary.

  protected val csvFileName: Option[String] =
    Option(System.getProperty(csvFilePropertyName))

  // TODO: The next few methods have been copied as-is from the StatisticalTestSuite.
  //       Copying them should not be necessary.

  protected val repetitions: Int =
    Option(System.getProperty(repetitionsPropertyName)) match {
      case Some(reps) =>
        val intReps = reps.toInt

        failIf(
          s"Repetitions must be >= 1, but got $reps",
          intReps < 1)

        intReps
      case None =>
        val default = 1
        report(s"Repetitions defaults to $default.")

        default
    }

  override def getTestDirPath(testDir: String): Path = {
    failIf(s"Test directory '$testDir' does not exist", testDir == null)

    val targetPath: File = Paths.canonize(testDir)
    failIf(s"Invalid test directory '$testDir'", !targetPath.isDirectory)

    targetPath.toPath
  }

  override def beforeAll(): Unit = {
    super.beforeAll()

    csvFileName foreach (filename => {
      report(s"Recording verification times in ${filename}.")

      csvFile = new BufferedWriter(new FileWriter(filename))

      csvFile.write("File,Outputs,Mean [ms],StdDev [ms],RelStdDev [%],Best [ms],Median [ms],Worst [ms]")
      csvFile.newLine()
      csvFile.flush()
    })
  }

  override def afterAll(): Unit = {
    super.afterAll()

    csvFileName foreach (filename => {
      csvFile.close()

      report(s"Recorded verification times in ${filename}.")
    })
  }

  private def printableTimings(timings: Seq[Long], phaseNames: Seq[String]): String =
    timings.map(TimingUtils.formatTimeForTable).zip(phaseNames).map(tup => tup._1 + " (" + tup._2 + ")").mkString(", ")

  private def printablePercentage(percentage: Seq[Long], phaseNames: Seq[String]): String = {
    percentage
      .map(p => "%6s %%   ".format(p)) /** Format in sync with [[TimingUtils.formatTimeForTable()]] */
      .zip(phaseNames)
      .map(tup => tup._1 + " (" + tup._2 + ")")
      .mkString(", ")
  }

  private def failIf(message: => String, condition: Boolean): Unit =
    if (condition) fail(message)
}

private final case class TestRunData(outputs: Vector[AbstractOutput],
                                     durationRecord: VerificationDurationRecord,
                                     totalRuntime: Long)