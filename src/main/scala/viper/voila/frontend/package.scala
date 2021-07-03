/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import java.nio.file.Paths
import org.bitbucket.inkytonik.kiama.relation.Tree
import org.bitbucket.inkytonik.kiama.util.{FileSource, Position}
import viper.silver.ast.{LineColumnPosition, SourcePosition}

package object frontend {
  type VoilaTree = Tree[PAstNode, PProgram]

  val defaultPrettyPrinter = new DefaultPrettyPrinter

  def translate(position: Position): SourcePosition = {
    val path =
      position.source match {
        case FileSource(filename, _) => Paths.get(filename)
        case other => sys.error(s"Unexpected source: $other")
      }

    new SourcePosition(
      path,
      LineColumnPosition(position.line, position.column),
      None)
  }
}
