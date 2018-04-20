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
  private var comprehensionPatterns: Map[vpr.Exp, vpr.Function] = Map.empty

  def recordedSetComprehensions: Map[PSetComprehension, vpr.Function] = comprehensions

  def recordedSetComprehensionFunctions: Seq[vpr.Function] = comprehensionPatterns.values.toSeq

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
    val decls: ListSet[vpr.LocalVarDecl] =
      freeVariables.zipWithIndex
        .map{ case (fv,ix)  => {
        val vprDecl =
          vpr.LocalVarDecl(
              s"$$s_$ix",// fv.name,
            vprElementType
          )()

          vprDecl
        }}(breakOut)

    val freeVariablesToDecls: ListMap[PIdnUse, vpr.LocalVarDecl] =
      freeVariables.zip(decls)(breakOut)

    val vprBody = {
      val vprQVarDecl =
        vpr.LocalVarDecl(
          "$k", // comprehension.qvar.id.name,
          vprElementType
        )()

      val vprSetConstraint =
        vpr.EqCmp(
          vpr.AnySetContains(
            vprQVarDecl.localVar,
            vpr.Result()(typ = vprSetType)
          )(),
          translateWith(comprehension.filter) {
            case PIdnExp(id) if id.name == comprehension.qvar.id.name =>
              vprQVarDecl.localVar

            case PIdnExp(id) if freeVariables.contains(id) =>
              freeVariablesToDecls(id).localVar
          }
        )()

      vpr.Forall(
        variables = Vector(vprQVarDecl),
        triggers = Vector.empty,
        exp = vprSetConstraint
      )()
    }

    val vprFunction = if (comprehensionPatterns.contains(vprBody)) {
      comprehensionPatterns(vprBody)
    } else {
      val function = vpr.Function(
        name = setComprehensionFunctionName,
        formalArgs = decls.toSeq,
        typ = vprSetType,
        pres = Vector.empty,
        posts = Vector(vprBody),
        decs = None,
        body = None
      )()

      comprehensionPatterns += vprBody -> function

      function
    }

    comprehensions += comprehension -> vprFunction
  }
}
