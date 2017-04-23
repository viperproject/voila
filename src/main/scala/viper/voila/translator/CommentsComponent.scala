/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver.{ast => vpr}

trait CommentsComponent { this: PProgramToViperTranslator =>
  sealed trait SectionMarker
  object SectionMarker {
    case object Begin extends SectionMarker { override val toString = "BEGIN" }
    case object Mid extends SectionMarker { override val toString = "MID" }
    case object End extends SectionMarker { override val toString = "END" }
  }

  def sectionComment(section: String, marker: SectionMarker): vpr.Seqn = {
    val pattern = "-"
    val rep = 7
    val span = 33
    val prefix = s"${pattern * rep} $section $marker"
    val comment = s"$prefix ${pattern * (span - prefix.length - 1)}"
    val info = vpr.SimpleInfo(Vector("", comment))

    vpr.Seqn(Vector.empty)(info = info)
  }

  def surroundWithSectionComments(sectionName: String, statement: vpr.Stmt): vpr.Stmt =
    surroundWithSectionComments(sectionName, Vector(statement))

  def surroundWithSectionComments(sectionName: String, statements: Vector[vpr.Stmt]): vpr.Stmt = {
    vpr.Seqn(
         sectionComment(sectionName, SectionMarker.Begin)
      +: statements
      :+ sectionComment(sectionName, SectionMarker.End)
    )()
  }
}