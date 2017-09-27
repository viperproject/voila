/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.reporting

import org.bitbucket.inkytonik.kiama.util.Position
import viper.voila.VoilaGlobalState
import viper.voila.frontend.PAstNode

sealed trait VoilaError {
  def position: Position
  def message: String
  def id: String

  def formattedMessage: String =
    s"$message (${position.line}:${position.column})"

  override lazy val toString: String = formattedMessage
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
abstract class AbstractVerificationError extends VerificationError {
  lazy val position: Position = VoilaGlobalState.positions.getStart(offendingNode).get
}

case class AssignmentError(offendingNode: PAstNode, reason: String)
    extends AbstractVerificationError {

  def id: String = "assignment.error"
  val message: String = s"Assignment might fail: $reason"
}

case class PostconditionError(offendingNode: PAstNode, reason: String)
    extends AbstractVerificationError {

  def id: String = "postcondition.error"
  val message: String = s"Postcondition might not hold: $reason"
}

case class PreconditionError(offendingNode: PAstNode, reason: String)
    extends AbstractVerificationError {

  def id: String = "precondition.error"
  val message: String = s"Precondition might not hold: $reason"
}
