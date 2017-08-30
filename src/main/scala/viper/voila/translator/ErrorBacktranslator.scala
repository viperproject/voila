/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver
import viper.voila.frontend._
import viper.silver.verifier.{errors => vprerr, reasons => vprrea}
import viper.voila.reporting.{AssignmentFailed, UnhandledViperError, VoilaFailure}

trait ErrorBacktranslator {
  def translate(error: silver.verifier.VerificationError): VoilaFailure
}

class DefaultErrorBacktranslator extends ErrorBacktranslator {
  def translate(error: viper.silver.verifier.VerificationError): VoilaFailure = {
    error match {
      case vprerr.AssignmentFailed(Source(sourceNode: PHeapRead), reason, _) =>
        AssignmentFailed(PIdnExp(sourceNode.lhs), translate(reason))
      case vprerr.AssignmentFailed(Source(sourceNode: PHeapWrite), reason, _) =>
        AssignmentFailed(PIdnExp(sourceNode.location), translate(reason))
      case vprerr.AssignmentFailed(Source(sourceNode: PAssign), reason, _) =>
        AssignmentFailed(PIdnExp(sourceNode.lhs), translate(reason))
      case _ =>
        UnhandledViperError(error)
    }
  }

  private def translate(reason: silver.verifier.ErrorReason): String = {
    reason match {
      case vprrea.InsufficientPermission(node) =>
        s"There might be insufficient permission to access ${source(node)}"
      case _=>
        reason.readableMessage
    }
  }

  private def source(node: silver.ast.Node): String = {
    node match {
      case Source(sourceNode) => sourceNode.format
      case _ => node.toString()
    }
  }

  object Source {
    def unapply(node: silver.ast.Node): Option[PAstNode] = {
      val info = node.getPrettyMetadata._2

      println("\n[Source]")
      println(s"  info = $info")

      info.getUniqueInfo[SourceInfo] match {
        case Some(SourceInfo(sourceNode)) =>
          println(s"  sourceNode = $sourceNode")
          Some(sourceNode)
        case None => None
      }
    }
  }
}