/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.reporting

import org.bitbucket.inkytonik.kiama.util.Positions
import viper.voila.frontend.PAstNode

sealed trait VoilaResult

case object Success extends VoilaResult

sealed trait VoilaFailure extends VoilaResult {
  def offendingNode: PAstNode

  def message: String

  def message(positions: Positions): String = {
    val formattedPosition: String =
      positions.getStart(offendingNode) match {
        case Some(pos) => s"${pos.line}:${pos.column}"
        case None => "<unknown position>"
      }
    
    s"$message ($formattedPosition)"
  }
}

case class AssignmentFailed(offendingNode: PAstNode, reason: String) extends VoilaFailure {
  val message: String = s"Assignment failed: $reason"
}
