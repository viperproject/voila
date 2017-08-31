/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import viper.silver

//trait SystemUnderTest {
//  /** For filtering test annotations. Does not need to be unique. */
//  val projectInfo: ProjectInfo
//
//  def run(input: AnnotatedTestInput): Seq[AbstractOutput]
//}

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

class VoilaTests extends silver.testing.AnnotationBasedTestSuite {
  val voilaInstance: Voila = _

  val voilaInstanceUnderTest: viper.silver.testing.SystemUnderTest = ???

  def systemsUnderTest: Seq[silver.testing.SystemUnderTest] = Vector(voilaInstanceUnderTest)


  def testDirectories = ???
}
