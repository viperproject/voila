/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.reporting

import org.bitbucket.inkytonik.kiama.util.{Position, Positions}
import viper.voila.VoilaGlobalState
import viper.voila.frontend.PAstNode

sealed trait VoilaResult

case object Success extends VoilaResult

case class Failure(errors: Vector[VoilaError]) extends VoilaResult



sealed trait VoilaError {
  def position: Position
  def message: String
  def id: String

  def formattedMessage: String =
    s"$message (${position.line}:${position.column})"
}

case class ResourceError(message: String) extends VoilaError {
  val position: Position = null // TODO: Fix
  val id = "resource.error"
}

case class ParserError(message: String, position: Position) extends VoilaError {
  val id = "parser.error"
}

case class TypecheckerError(message: String, position: Position) extends VoilaError {
  val id = "typechecker.error"
}

sealed trait VerificationError extends VoilaError {
  def offendingNode: PAstNode

  def message: String

//  def message(positions: Positions): String = {
//    val formattedPosition: String =
//      positions.getStart(offendingNode) match {
//        case Some(pos) => s"${pos.line}:${pos.column}"
//        case None => "<unknown position>"
//      }
//
//    s"$message ($formattedPosition)"
//  }
}

// TODO: Remove dependency on global state (for positions)

case class AssignmentFailed(offendingNode: PAstNode, reason: String) extends VerificationError {
  def position: Position = VoilaGlobalState.positions.getStart(offendingNode).get
  def id: String = "assignment.failed"
  val message: String = s"Assignment failed: $reason"
}
