/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import viper.silver
import viper.silver.testing._

//private case class VerifierUnderTest(verifier: Verifier)
//    extends SystemUnderTest with TimingUtils {
//
//    val projectInfo: ProjectInfo = SilSuite.this.projectInfo.update(verifier.name)
//
//    def run(input: AnnotatedTestInput): Seq[AbstractOutput] = {
//      val fe = frontend(verifier, input.files)
//      val tPhases = fe.phases.map { p =>
//        time(p.action)._2 + " (" + p.name + ")"
//      }.mkString(", ")
//      info(s"Verifier used: ${verifier.name} ${verifier.version}.")
//      info(s"Time required: $tPhases.")
//      val actualErrors = fe.result match {
//        case Success => Nil
//        case Failure(es) => es collect {
//          case e: AbstractVerificationError =>
//            e.transformedError()
//          case rest: AbstractError => rest
//        }
//      }
//      actualErrors.map(SilOutput)
//    }
//  }

//case class SilOutput(error: AbstractError) extends AbstractOutput {
//  def isSameLine(file: Path, lineNr: Int): Boolean = error.pos match {
//    case p: SourcePosition => lineNr == p.line
//    case p: TranslatedPosition => file == p.file && lineNr == p.line
//    case _ => false
//  }
//
//  def fullId: String = error.fullId
//
//  override def toString: String = error.toString
//}

class VoilaTests extends AnnotationBasedTestSuite {
  val voilaInstance: Voila = null

  val voilaInstanceUnderTest: SystemUnderTest =
    new SystemUnderTest with TimingUtils {
      val projectInfo: ProjectInfo = new ProjectInfo(List("Voila"))

      def run(input: AnnotatedTestInput):Seq[AbstractOutput] = {

      }
    }

  def systemsUnderTest: Seq[silver.testing.SystemUnderTest] = Vector(voilaInstanceUnderTest)

  def testDirectories: Seq[String] = Vector("regressions")
}
