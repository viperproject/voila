/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.reporting

import org.bitbucket.inkytonik.kiama.util.Position
import viper.voila.VoilaGlobalState
import viper.voila.frontend._

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
  type OffendingNode <: PAstNode
  def offendingNode: OffendingNode
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

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError

  def dueTo(detailToAppend: VerificationError): VerificationError =
    detail match {
      case None => dup(offendingNode, Some(detailToAppend))
      case Some(det) => dup(offendingNode, Some(det dueTo detailToAppend))
    }

  def id: String =
    detail match {
      case None => localId
      case Some(_detail) => s"$localId:${_detail.id}"
    }

  def message: String =
    detail match {
      case None => s"$localMessage."
      case Some(_detail) => s"$localMessage. ${_detail.message}"
    }
}

case class AssignmentError(offendingNode: PStatement, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PStatement
  def localId: String = "assignment_error"
  val localMessage: String = "Assignment might fail"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class PostconditionError(offendingNode: PExpression, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PExpression
  def localId: String = "postcondition_error"
  val localMessage: String = "Postcondition might not hold"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class PreconditionError(offendingNode: PProcedureCall, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PProcedureCall
  def localId: String = "precondition_error"
  val localMessage: String = "Precondition might not hold"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class AssertError(offendingNode: PExpression, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PExpression
  def localId: String = "assert_error"
  val localMessage: String = "Assert might fail"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class UseAtomicError(offendingNode: PUseAtomic, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PUseAtomic
  def localId: String = "use-atomic_error"
  val localMessage: String = "Rule use-atomic might fail"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class MakeAtomicError(offendingNode: PMakeAtomic, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PMakeAtomic
  def localId: String = "make-atomic_error"
  val localMessage: String = "Rule make-atomic might fail"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class UpdateRegionError(offendingNode: PUpdateRegion, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PUpdateRegion
  def localId: String = "update-region_error"
  val localMessage: String = "Rule update-region might fail"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientPermissionError(offendingNode: PExpression, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PExpression
  def localId: String = "permission_error"
  val localMessage: String = s"Insufficient permission to $offendingNode"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class AssertionError(offendingNode: PExpression, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PExpression
  def localId: String = "assertion_error"
  val localMessage: String = s"Assertion $offendingNode might not hold"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InterferenceError(offendingNode: PInterferenceClause, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PInterferenceClause
  def localId: String = "interference_error"
  val localMessage: String = s"Interference '$offendingNode' might not hold"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientRegionPermissionError(offendingNode: PExpression, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PExpression
  def localId: String = "region_permission_error"
  val localMessage: String = s"Region $offendingNode might not be accessible"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class RegionStateError(offendingNode: PExpression, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PExpression
  def localId: String = "region_state_error"
  val localMessage: String = s"Region $offendingNode might not be in the expected state"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientGuardPermissionError(offendingNode: PGuardExp, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PGuardExp
  def localId: String = "guard_permission_error"
  val localMessage: String = s"Guard $offendingNode might not be available"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
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

case class IllegalRegionStateChangeError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PAstNode
  def localId: String = "illegal_state_change_error"
  val localMessage: String = "Region state change may not be allowed"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class MissingRegionStateChangeError(offendingNode: PPredicateExp, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PPredicateExp
  def localId: String = "missing_state_change_error"
  val localMessage: String = s"Region state might not change, but is expected to"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}


case class MiscellaneousError(localMessage: String,
                              offendingNode: PAstNode,
                              detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PAstNode
  def localId: String = "misc_error"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(localMessage, offendingNode, detail)
}
