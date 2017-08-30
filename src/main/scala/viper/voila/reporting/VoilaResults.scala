/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.reporting

import viper.voila.frontend.PExpression

sealed trait VoilaResult

case object Success extends VoilaResult

sealed trait VoilaFailure extends VoilaResult {
  def message: String
}

case class AssignmentFailed(lhs: PExpression, reason: String) extends VoilaFailure {
  def message: String = s"Assignment to $lhs failed. $reason"
}
