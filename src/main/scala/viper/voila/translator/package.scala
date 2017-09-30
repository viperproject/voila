/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import viper.silver
import viper.voila.frontend.{DefaultPrettyPrinter, PAstNode, PrettyPrinter}
import viper.voila.reporting.VerificationError
import viper.silver.{ast => vpr}

package object translator {
  type ErrorTransformer = PartialFunction[silver.verifier.VerificationError, VerificationError]
  type ReasonTransformer = PartialFunction[silver.verifier.ErrorReason, VerificationError]

  implicit class RichViperNode[N <: vpr.Node](node: N) {
    def withSource(source: PAstNode): N = {
      val (pos, info, errT) = node.getPrettyMetadata

      require(info == vpr.NoInfo)
      require(pos == vpr.NoPosition)

      val newInfo = SourceInfo(source)
      val newPos = vpr.TranslatedPosition(source.position)

      node.duplicateMeta((newPos, newInfo, errT)).asInstanceOf[N]
    }
  }

  case class SourceInfo(source: PAstNode) extends vpr.Info {
    def comment: Seq[String] = Vector.empty
  }

  implicit val prettyPrinter: PrettyPrinter = new DefaultPrettyPrinter
}
