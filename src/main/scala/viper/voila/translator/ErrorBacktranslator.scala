/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver
import viper.voila.frontend._
import viper.silver.verifier.{errors => vprerr, reasons => vprrea}
import viper.voila.reporting.{AssignmentError, PostconditionError, VoilaError}

trait ErrorBacktranslator {
  def translate(error: silver.verifier.VerificationError): Option[VoilaError]
}

class DefaultErrorBacktranslator extends ErrorBacktranslator {
  def translate(error: viper.silver.verifier.VerificationError): Option[VoilaError] = {
    error match {
      case vprerr.AssignmentFailed(Source(sourceNode: PHeapRead), reason, _) =>
        Some(AssignmentError(sourceNode, translate(reason)))
      case vprerr.AssignmentFailed(Source(sourceNode: PHeapWrite), reason, _) =>
        Some(AssignmentError(sourceNode, translate(reason)))
      case vprerr.AssignmentFailed(Source(sourceNode: PAssign), reason, _) =>
        Some(AssignmentError(sourceNode, translate(reason)))
      case vprerr.PostconditionViolated(Source(node), _, reason) =>
        Some(PostconditionError(node, translate(reason)))
      case _ =>
        None
    }
  }

  private def translate(reason: silver.verifier.ErrorReason): String = {
    reason match {
      case vprrea.InsufficientPermission(node) =>
        s"There might be insufficient permission to *${source(node)}"
      case vprrea.AssertionFalse(node) =>
        s"Assertion ${source(node)} might not hold"
//      case vprrea.DummyReason =>
//      case vprrea.InternalReason(offendingNode, explanation) =>
//      case vprrea.FeatureUnsupported(offendingNode, explanation) =>
//      case vprrea.UnexpectedNode(offendingNode, explanation, stackTrace) =>
//      case vprrea.VariantNotDecreasing(offendingNode, decExp) =>
//      case vprrea.TerminationNoBound(offendingNode, decExp) =>
//      case vprrea.CallingNonTerminatingFunction(offendingNode, callee) =>
//      case vprrea.NoDecClauseSpecified(offendingNode) =>
//      case vprrea.EpsilonAsParam(offendingNode) =>
//      case vprrea.ReceiverNull(offendingNode) =>
//      case vprrea.DivisionByZero(offendingNode) =>
//      case vprrea.NegativePermission(offendingNode) =>
//      case vprrea.InvalidPermMultiplication(offendingNode) =>
//      case vprrea.MagicWandChunkNotFound(offendingNode) =>
//      case vprrea.NamedMagicWandChunkNotFound(offendingNode) =>
//      case vprrea.MagicWandChunkOutdated(offendingNode) =>
//      case vprrea.ReceiverNotInjective(offendingNode) =>
//      case vprrea.LabelledStateNotReached(offendingNode) =>
//      case vprrea.SeqIndexNegative(seq, offendingNode) =>
//      case vprrea.SeqIndexExceedsLength(seq, offendingNode) =>
      case _=>
        reason.readableMessage
    }
  }

  private def source(node: silver.ast.Node): String = {
    node match {
      case Source(sourceNode) => sourceNode.pretty
      case _ => node.toString()
    }
  }

  object Source {
    def unapply(node: silver.ast.Node): Option[PAstNode] = {
      val info = node.getPrettyMetadata._2

//      println(s"Off. node: $node")
//      println(s"  Info: $info")

      info.getUniqueInfo[SourceInfo] match {
        case Some(SourceInfo(sourceNode)) =>
//          println(s"  Source: $sourceNode")
          Some(sourceNode)
        case None => None
      }
    }
  }
}
