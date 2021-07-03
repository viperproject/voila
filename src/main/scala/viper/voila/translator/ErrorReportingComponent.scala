/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.voila.frontend.PAstNode
import viper.voila.reporting.AdditionalErrorClarification

trait ErrorReportingComponent { this: PProgramToViperTranslator =>
  def hintAtEnclosingLoopInvariants(of: PAstNode): Option[AdditionalErrorClarification] = {
    val loops = semanticAnalyser.enclosingLoops(of)

    if (loops.isEmpty) {
      None
    } else {
      val s = if (loops.tail.isEmpty) "" else "s"

      Some(
        AdditionalErrorClarification(
           "A common source of this problem are insufficient loop invariants, such as the " +
          s"invariant$s of the enclosing loop$s in line$s " +
          s"${loops.map(_.position.line).mkString(",")}",
          of))
    }
  }
}
