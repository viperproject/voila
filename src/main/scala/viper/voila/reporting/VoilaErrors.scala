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
  def dueTo(detailToAppend: Option[VerificationError]): VerificationError

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

/* TODO: Remove dependency on global state (for positions) */
sealed abstract class AbstractVerificationError extends VerificationError {
  lazy val position: Position = VoilaGlobalState.positions.getStart(offendingNode).get

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError

  def dueTo(detailToAppend: VerificationError): VerificationError =
    detail match {
      case None => dup(offendingNode, Some(detailToAppend))
      case Some(det) => dup(offendingNode, Some(det dueTo detailToAppend))
    }

  def dueTo(detailToAppend: Option[VerificationError]): VerificationError =
    detailToAppend match {
      case Some(det) => dueTo(det)
      case None => this
    }

  def id: String =
    detail match {
      case None => localId
      case Some(_: AdditionalErrorClarification) => localId
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

case class AllocationError(offendingNode: PNewStmt, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PNewStmt
  def localId: String = "allocation_error"
  val localMessage: String = "Allocation might fail"

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

case class AssertError(offendingNode: PAssert, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PAssert
  def localId: String = "assert_error"
  val localMessage: String = "Assert might fail"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class ExhaleError(offendingNode: PExhale, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PExhale
  def localId: String = "exhale_error"
  val localMessage: String = "Exhale might fail"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class FoldError(offendingNode: PFold, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PFold
  def localId: String = "fold_error"
  val localMessage: String = "Fold might fail"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class UnfoldError(offendingNode: PUnfold, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PUnfold
  def localId: String = "unfold_error"
  val localMessage: String = "Unfold might fail"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class LoopInvariantPreservationError(offendingNode: PInvariantClause, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PInvariantClause
  def localId: String = "invariant_preservation_error"
  val localMessage: String = "Loop invariant might not be preserved"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class LoopInvariantEstablishmentError(offendingNode: PInvariantClause, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PInvariantClause
  def localId: String = "invariant_establishment_error"
  val localMessage: String = "Loop invariant might not be established"

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

case class MakeAtomicProcedureError(offendingNode: PProcedure, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PProcedure
  def localId: String = "make-atomic-procedure_error"
  val localMessage: String = "make-atomic-procedure might fail"

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

case class OpenRegionError(offendingNode: POpenRegion, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = POpenRegion
  def localId: String = "open-region_error"
  val localMessage: String = "Rule open-region might fail"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientPermissionError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
        /* TODO: offendingNode's type should allow resources only, not any node */
    extends AbstractVerificationError {

  type OffendingNode = PAstNode
  def localId: String = "permission_error"
  val localMessage: String = s"Permission to ${offendingNode.formatForUsers} might not suffice"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class AssertionError(offendingNode: PExpression, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PExpression
  def localId: String = "assertion_error"
  val localMessage: String = s"Assertion ${offendingNode.formatForUsers} might not hold"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InterferenceError(offendingNode: PInterferenceClause, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PInterferenceClause
  def localId: String = "interference_error"
  val localMessage: String = s"Interference clause '${offendingNode.formatForUsers}' might not hold"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class CalleeLevelTooHighError(offendingNode: PProcedureCall, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PProcedureCall
  def localId: String = "callee_level_too_high_error"
  val localMessage: String = s"The current level might be too low to call '${offendingNode.formatForUsers}'"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class CalleeAtomicityContextError(offendingNode: PProcedureCall, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PProcedureCall
  def localId: String = "callee_atomicity_context_error"
  val localMessage: String = s"The atomicity context of the called procedure '${offendingNode.formatForUsers}' might contain a currently updated region"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InspectLevelTooHighError(offendingNode: PPredicateExp, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PPredicateExp
  def localId: String = "inspect_level_too_high_error"
  val localMessage: String = s"The current level might be too low to apply an inspection rule on region '${offendingNode.formatForUsers}'"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientRegionPermissionError(offendingNode: PPredicateExp, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PPredicateExp
  def localId: String = "region_permission_error"
  val localMessage: String = s"Region ${offendingNode.formatForUsers} might not be accessible"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

// TODO: Make offendingNode should be less generic
case class RegionStateError(offendingNode: PAstNode, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PAstNode
  def localId: String = "region_state_error"
  val localMessage: String = s"Region ${offendingNode.formatForUsers} might not be in the expected state"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class RegionInterpretationNotStableError(offendingNode: PRegion, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PRegion
  def localId: String = "region_interpretation_not_stable_error"
  val localMessage: String = s"The interpretation of region ${offendingNode.id.name} might not be stable"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class MethodLevelNegativeError(offendingNode: PProcedure, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PProcedure
  def localId: String = "method_level_negative_error"
  val localMessage: String = s"The level clause expression of method ${offendingNode.id.name} might not be positive"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class MethodPreconditionNotStableError(offendingNode: PProcedure, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PProcedure
  def localId: String = "method_precondition_not_stable_error"
  val localMessage: String = s"The precondition of method ${offendingNode.id.name} might not be stable"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class MethodPostconditionNotStableError(offendingNode: PProcedure, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PProcedure
  def localId: String = "method_postcondition_not_stable_error"
  val localMessage: String = s"The postcondition of method ${offendingNode.id.name} might not be stable"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class ActionNotTransitiveError(offendingNode: PAction, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PAction
  def localId: String = "action_not_transitive_error"
  val localMessage: String = s"The action ${offendingNode.formatForUsers} might not be transitive"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class RegionActionsNotTransitiveError(offendingNode: PRegion, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PRegion
  def localId: String = "region_actions_not_transitive_error"
  val localMessage: String = s"The actions of region ${offendingNode.id.name} might not be transitive"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class RegionAtomicityContextTrackingError(offendingNode: PPredicateExp, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PPredicateExp
  def localId: String = "region_atomicity_context_tracking_error"
  val localMessage: String = s"Use_Atomic or Make_Atomic might have already been applied to Region ${offendingNode.formatForUsers}"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientRegionAtomicityContextTrackingError(offendingNode: PPredicateExp, detail: Option[VerificationError] = None)
  extends AbstractVerificationError {

  type OffendingNode = PPredicateExp
  def localId: String = "region_atomicity_context_tracking_permission_error"
  val localMessage: String = s"Not enough permission to access atomicity context for region ${offendingNode.formatForUsers}"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientGuardPermissionError(offendingNode: PRegionedGuardExp, detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PRegionedGuardExp
  def localId: String = "guard_permission_error"
  val localMessage: String = s"Guard ${offendingNode.formatForUsers} might not be available"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, detail)
}

case class InsufficientDiamondResourcePermissionError(offendingNode: PPredicateExp,
                                                      regionId: PIdnNode,
                                                      detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PPredicateExp
  def localId: String = "diamond_permission_error"
  val localMessage: String = s"Diamond resource $regionId |=> <D> might not be available"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, regionId, detail)
}

case class InsufficientTrackingResourcePermissionError(offendingNode: PPredicateExp,
                                                       regionId: PIdnNode,
                                                       detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PPredicateExp
  def localId: String = "tracking_permission_error"
  val localMessage: String = s"Tracking resource $regionId |=> (_, _) might not be available"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(offendingNode, regionId, detail)
}

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

/** Do not use this error as the main error, only append it to one of the proper errors
  * defined above.
  *
  * TODO: 1. Don't make [[AdditionalErrorClarification]] extend [[AbstractVerificationError]]
  *       2. Change proper errors above s.t. field detail is of type
  *          `Option[Either[VerificationError,AdditionalErrorClarification]]`
  *       3. Change AdditionalErrorClarification.detail to be of type
  *          `Option[AdditionalErrorClarification]`
  */
case class AdditionalErrorClarification(localMessage: String,
                                        offendingNode: PAstNode,
                                        detail: Option[VerificationError] = None)
    extends AbstractVerificationError {

  type OffendingNode = PAstNode
  def localId: String = "additional_error_clarification"

  protected def dup(offendingNode: OffendingNode, detail: Option[VerificationError]): VerificationError =
    copy(localMessage, offendingNode, detail)
}
