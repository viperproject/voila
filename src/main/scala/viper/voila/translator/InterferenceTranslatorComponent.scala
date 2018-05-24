/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver.ast.{Exp, LocalVar, LocalVarDecl, Type}

import scala.collection.{breakOut, mutable}
import viper.silver.{ast => vpr}
import viper.silver.verifier.{errors => vprerr, reasons => vprrea}
import viper.voila.backends.ViperAstUtils
import viper.voila.frontend._
import viper.voila.reporting.{FoldError, InsufficientRegionPermissionError, InterferenceError, PreconditionError, RegionStateError, UnfoldError}


trait InterferenceTranslatorComponent { this: PProgramToViperTranslator =>

  val interferenceSetFunctionManager: TranslatorUtils.BasicFootprintFunctionManagerNoFeature[PRegion] with TranslatorUtils.EmptyFootprintSelection[PRegion]  =
    new TranslatorUtils.BasicFootprintFunctionManagerNoFeature[PRegion]
      with TranslatorUtils.EmptyFootprintSelection[PRegion]
      with TranslatorUtils.MemberBasedFootprintNames[PRegion] {

      override val name: String = "interference"

      override def functionArgSelection(obj: PRegion): Vector[LocalVarDecl] = obj.formalInArgs map translate
      override def selectFunctionArgs(obj: PRegion, args: Vector[Exp]): Vector[Exp] = args
      override def functionTyp(obj: PRegion): Type = vpr.SetType(regionStateFunction(obj).typ)
    }

  /* Interference-Set Domain and Domain-Functions */


  def interfereceWrapperExtension(region: PRegion, postState: Vector[vpr.Exp] => vpr.Exp)
                                 (selectWrapper: QuantifierWrapper.StmtWrapper): QuantifierWrapper.StmtWrapper = {

    val varName = "$_m" // TODO: naming convention
    val varType = regionStateFunction(region).typ
    val varDecl = vpr.LocalVarDecl(varName, varType)()
    val variable = varDecl.localVar

    val regionArgs = selectWrapper.param
    val newState = postState(regionArgs)

    /* exp in X(xs)*/
    def expInSet(exp: vpr.Exp) = vpr.AnySetContains(
      exp,
      interferenceSetFunctionManager.functionApplication(region, regionArgs)
    )()

    /* m in X(xs) <==> e(xs)[postState(xs) -> m] */
    def pre(exp: vpr.Exp): vpr.Exp = {
      val substExp = exp.transform{ case `newState` => variable}
      vpr.EqCmp(expInSet(variable), substExp)()
    }

    /* inhale exp; Q(postState(xs) in X(xs)) */
    def post(exp: vpr.Exp): vpr.Stmt = {
      val selectSet = vpr.Inhale(exp)()
      val selectState = selectWrapper.wrap(expInSet(newState))

      /* acc(R_inference_fp()) */
      val interferenceFootprintAccess =
        interferenceSetFunctionManager.footprintAccess(region)

      /* exhale acc(R_inference_fp()) */
      val vprExhaleInterferenceFootprintAccess =
        vpr.Exhale(interferenceFootprintAccess)()

      /* inhale acc(R_inference_fp()) */
      val vprInhaleInterferenceFootprintAccess =
        vpr.Inhale(interferenceFootprintAccess)()

      vpr.Seqn(
        Vector(
          vprExhaleInterferenceFootprintAccess,
          vprInhaleInterferenceFootprintAccess,
          selectSet,
          selectState
        ),
        Vector.empty
      )()
    }

    val triggers = Vector(vpr.Trigger(Vector(expInSet(variable)))())

    QuantifierWrapper.AllWrapper(Vector(varDecl), regionArgs, triggers)(post, pre)
  }


  def initInterference(statement: vpr.Stmt): vpr.Stmt = {
    ???
  }

  def linkInterference() = ???

  def queryInterference() = ???

}
