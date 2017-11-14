/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver.{ast => vpr}
import viper.voila.frontend.{PSetComprehension, VoilaTree}

trait SetComprehensionComponent { this: PProgramToViperTranslator =>
  private var comprehensions: Map[PSetComprehension, vpr.Function] = Map.empty

  def recordedSetComprehensions: Map[PSetComprehension, vpr.Function] = comprehensions

  def analyseSetComprehensions(tree: VoilaTree): Unit = {
    comprehensions = comprehensions.empty

    tree.nodes
      .collect { case comprehension: PSetComprehension => comprehension }
      .distinct
      .foreach (recordSetComprehension)
  }

  protected def recordSetComprehension(comprehension: PSetComprehension): Unit = {
    val setComprehensionFunctionName =
      freshIdentifier(s"comprehension_${comprehension.position.line}_${comprehension.position.column}")

    val vprElementType = translateNonVoid(semanticAnalyser.typeOfIdn(comprehension.qvar.id))
    val vprSetType = vpr.SetType(vprElementType)

    val vprFormalArgs =
      semanticAnalyser
        .freeVariables(comprehension)
        .map(idnuse =>
          vpr.LocalVarDecl(
            idnuse.name,
            vprElementType
          )())
        .toSeq

    val vprBody = {
      val vprQVarDecl =
        vpr.LocalVarDecl(
          comprehension.qvar.id.name,
          vprElementType
        )()

      val vprSetConstraint =
        vpr.EqCmp(
          vpr.AnySetContains(
            vprQVarDecl.localVar,
            vpr.Result()(typ = vprSetType)
          )(),
          translate(comprehension.filter)
        )()

      vpr.Forall(
        variables = Vector(vprQVarDecl),
        triggers = Vector.empty,
        exp = vprSetConstraint
      )()
    }

    val vprFunction =
      vpr.Function(
        name = setComprehensionFunctionName,
        formalArgs = vprFormalArgs,
        typ = vprSetType,
        pres = Vector.empty,
        posts = Vector(vprBody),
        decs = None,
        body = None
      )()

    comprehensions += comprehension -> vprFunction
  }
}