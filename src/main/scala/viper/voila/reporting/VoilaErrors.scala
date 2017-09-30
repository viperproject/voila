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

  override def toString: String = formattedMessage
}

case class ResourceError(message: String) extends VoilaError {
  val position: Position = null // TODO: Fix
  val id = "resource_error"
}

case class ParserError(message: String, position: Position) extends VoilaError {
  val id = "parser_error"
}

case class TypecheckerError(message: String, position: Position) extends VoilaError {
  val id = "typechecker_error"
}

sealed trait VerificationError extends VoilaError {
  def offendingNode: PAstNode
  def localId: String
  def localMessage: String
  def detail: Option[VerificationError]
  def dueTo(detailToAppend: VerificationError): VerificationError

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
sealed abstract class AbstractVerificationError extends VerificationError {
  lazy val position: Position = VoilaGlobalState.positions.getStart(offendingNode).get

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError

  def dueTo(detailToAppend: VerificationError): VerificationError =
    detail match {
      case None => dup(offendingNode, Some(detailToAppend))
      case Some(det) => det dueTo detailToAppend
    }

  def id: String =
    detail match {
      case None => localId
      case Some(_detail) => s"$localId:${_detail.id}"
    }

  def message: String =
    detail match {
      case None => s"$localMessage."
      case Some(_detail) => s"$localMessage: ${_detail.message}"
    }
}

case class AssignmentError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "assignment_error"
  val localMessage: String = "Assignment might fail"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class PostconditionError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "postcondition_error"
  val localMessage: String = "Postcondition might not hold"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class PreconditionError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "precondition_error"
  val localMessage: String = "Precondition might not hold"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class AssertError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "assert_error"
  val localMessage: String = "Assert might fail"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class UseAtomicError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "use-atomic_error"
  val localMessage: String = "Rule use-atomic might fail"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class MakeAtomicError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "make-atomic_error"
  val localMessage: String = "Rule make-atomic might fail"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class UpdateRegionError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "update-region_error"
  val localMessage: String = "Rule update-region might fail"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientPermissionError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "permission_error"
  val localMessage: String = s"Insufficient permission to $offendingNode"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class AssertionError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "assertion_error"
  val localMessage: String = s"Assertion $offendingNode might not hold"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InterferenceError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "interference_error"
  val localMessage: String = s"Interference '$offendingNode' might not hold"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientRegionPermissionError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "region_permission_error"
  val localMessage: String = s"Region $offendingNode might not be accessible"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class RegionStateError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "region_state_error"
  val localMessage: String = s"Region $offendingNode might not be in the expected state"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientGuardPermissionError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "guard_permission_error"
  val localMessage: String = s"Guard $offendingNode might not be available"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

//case class RegionPredicateError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
//    extends AbstractVerificationError {
//
//  def id: String = "region.predicate.error"
//  val localMessage: String = s"Region predicate $offendingNode might not be available"
//
//  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
//    copy(offendingNode, detail)
//}

case class RegionStateChangeError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  def localId: String = "region_state_change_error"
  val localMessage: String = s"Performed region state change not permitted"

  protected def dup(offendingNode: PAstNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}