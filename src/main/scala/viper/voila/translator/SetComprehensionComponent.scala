/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.breakOut
import scala.collection.immutable.{ListMap, ListSet}
import viper.silver.{ast => vpr}
import viper.voila.frontend.{PIdnExp, PIdnUse, PSetComprehension, VoilaTree}

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

    val vprElementType = translate(semanticAnalyser.typeOfIdn(comprehension.qvar.id))
    val vprSetType = vpr.SetType(vprElementType)

    val freeVariables: ListSet[PIdnUse] = semanticAnalyser.freeVariables(comprehension)

    val freeVariablesToDecls: ListMap[PIdnUse, vpr.LocalVarDecl] =
      freeVariables
        .map(fv => {
          val vprDecl =
            vpr.LocalVarDecl(
              fv.name,
              vprElementType
            )()

          fv -> vprDecl
        })(breakOut)

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
          translateWith(comprehension.filter) {
            case exp @ PIdnExp(id) if freeVariables.contains(id) =>
              freeVariablesToDecls(id).localVar
          }
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
        formalArgs = freeVariablesToDecls.values.toSeq,
        typ = vprSetType,
        pres = Vector.empty,
        posts = Vector(vprBody),
        decs = None,
        body = None
      )()

    comprehensions += comprehension -> vprFunction
  }
}
