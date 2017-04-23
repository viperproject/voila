/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.voila.frontend._
import viper.silver.{ast => vpr}

trait RuleTranslatorComponent { this: PProgramToViperTranslator =>
  sealed trait SectionMarker
  object SectionMarker {
    case object Begin extends SectionMarker { override val toString = "BEGIN" }
    case object Mid extends SectionMarker { override val toString = "MID" }
    case object End extends SectionMarker { override val toString = "END" }
  }

  def sectionComment(section: String, marker: SectionMarker): vpr.Seqn = {
    val pattern = "-"
    val rep = 7
    val prefix = s"${pattern * rep} $section $marker"
    val comment = s"$prefix ${pattern * (rep - prefix.length - 1)}"
    val info = vpr.SimpleInfo(Vector("", comment))

    vpr.Seqn(Vector.empty)(info = info)
  }

  def translate(makeAtomic: PMakeAtomic): vpr.Stmt = {
    val ruleName = "make-atomic"
    val beginComment = sectionComment(ruleName, SectionMarker.Begin)
    val endComment = sectionComment(ruleName, SectionMarker.Begin)

    val region =
      semanticAnalyser.entity(makeAtomic.regionPredicate.predicate).asInstanceOf[RegionEntity]
                      .declaration

    val regionArguments =
      makeAtomic.regionPredicate.arguments.init

    val inhaleDiamond =
      vpr.Inhale(diamondAccess(translateUseOf(makeAtomic.guard.regionId)))()

    val exhaleGuard =
      vpr.Exhale(translate(makeAtomic.guard))()

    val havoc =
      havocRegion(
        region,
        regionArguments,
        semanticAnalyser.interferenceSpecifications(makeAtomic)(makeAtomic).head.set,
        tmpVar(semanticAnalyser.typ(region.state)).localVar)

    vpr.Seqn(
      Vector(
        beginComment,
        inhaleDiamond,
        exhaleGuard,
        havoc,
        endComment)
    )()
  }

  def translate(updateRegion: PUpdateRegion): vpr.Stmt = {
    val ruleName = "update-region"
    val beginComment = sectionComment(ruleName, SectionMarker.Begin)
    val endComment = sectionComment(ruleName, SectionMarker.Begin)

    vpr.Seqn(Vector(beginComment, endComment))()
  }
}
