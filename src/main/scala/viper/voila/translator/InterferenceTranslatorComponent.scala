/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver.ast._

import scala.collection.{breakOut, mutable}
import viper.silver.{ast => vpr}
import viper.silver.verifier.{errors => vprerr, reasons => vprrea}
import viper.voila.backends.ViperAstUtils
import viper.voila.frontend._
import viper.voila.reporting.{FoldError, InsufficientRegionPermissionError, InterferenceError, PreconditionError, RegionStateError, UnfoldError}
import viper.voila.translator.TranslatorUtils._


trait InterferenceTranslatorComponent { this: PProgramToViperTranslator =>

  var evaluateInLastInfer: vpr.Exp => vpr.Exp = vpr.Old(_)()

  private var linkedRegions: List[(PRegion, Vector[PExpression], vpr.Label, Int)] = Nil

  def evaluateInterferenceContext(id: PIdnUse, origin: PExpression): vpr.Exp = {

    val dflt = translateUseOf(id).withSource(origin, overwrite = true)

    extractBoundedRegionInstance(id) match {
      case Some((region, inArgs, outArgs)) =>

        System.out.println("wawa")
        System.out.println(inArgs)
        System.out.println(currentlyOpenRegions)

        linkedRegions.find { case (r,in,l,v) => (r eq region) && (in eq inArgs)} match {
          case Some((_,_,l,v)) => vpr.LabelledOld(dflt, l.name)()
          case None => dflt
        }

      case _ => dflt
    }
  }

  val interferenceSetFunctions: HeapFunctionManager[PRegion] with RegionManager[vpr.Function, vpr.FuncApp] = {
    val _name = "interferenceSet"
    def _functionType(obj: PRegion): Type = vpr.SetType(regionStateFunction(obj).typ)

    val _footprintManager =
      new FootprintManager[PRegion]
        with RegionManager[vpr.Predicate, vpr.PredicateAccessPredicate]
        with RemoveVersionSelector[PRegion] {
        override val name: String = _name
      }
    val _triggerManager =
      new DomainFunctionManager[PRegion]
        with RegionManager[vpr.DomainFunc, vpr.DomainFuncApp]
        with SubFullSelector[PRegion] {
        override val name: String = _name
        override def functionTyp(obj: PRegion): Type = _functionType(obj)
      }

    collectedDeclarations ++= _triggerManager.collectGlobalDeclarations // TODO: this could be put into another trait

    new HeapFunctionManager[PRegion]
      with RegionManager[vpr.Function, vpr.FuncApp]
      with SequenceStabelizeVersionedSelector[PRegion] {

      override val footprintManager: FootprintManager[PRegion] with SubSelector[PRegion] = _footprintManager
      override val triggerManager: DomainFunctionManager[PRegion] with SubSelector[PRegion] = _triggerManager

      override def functionTyp(obj: PRegion): Type = _functionType(obj)
      override val name: String = _name

      override protected def post(trigger: DomainFuncApp): Vector[Exp] = {

        val varName = "$_m" // TODO: naming convention
        val varType = trigger.typ match { case vpr.SetType(t) => t }
        val varDecl = vpr.LocalVarDecl(varName, varType)()
        val variable = varDecl.localVar

        val varInResult =
          vpr.AnySetContains(
            variable,
            vpr.Result()(typ = trigger.typ)
          )()

        val varInTrigger =
          vpr.AnySetContains(
            variable,
            trigger
          )()

        val triggerRelation =
          vpr.Forall(
            Vector(varDecl),
            Vector(vpr.Trigger(Vector(varInResult))()),
            vpr.Implies(varInResult, varInTrigger)()
          )()

        val postCondition = vpr.InhaleExhaleExp(
          triggerRelation,
          vpr.TrueLit()()
        )()

        Vector(postCondition)
      }

      override def triggerApplication(id: PRegion, args: Vector[Exp]): Exp = selectArgs(id,args) match {
        case (xs :+ m) => vpr.AnySetContains(m, triggerManager.application(id, xs))()
      }
    }
  }



  def linkInterferenceContext(region: PRegion, args: Vector[vpr.Exp]): vpr.Stmt = {

    var counter = 0
    var tripples: List[(vpr.LocalVarDecl, PRegion, Vector[vpr.Exp])] = Nil

    val state = translateWith(region.state){
      case exp@ PIdnExp(id) =>

        extractBoundedRegionInstance(id) match {
          case Some((innerRegion, inArgs, outArgs)) =>

            val varName = s"$$_m${counter}" // TODO: naming convention
            counter += 1

            val regionStateType = translate(semanticAnalyser.typ(innerRegion.state))
            val varDecl = vpr.LocalVarDecl(varName, regionStateType)()
            val variable = varDecl.localVar

            tripples ::= (varDecl, innerRegion, inArgs map translate)

            variable

          case _ => translateUseOf(id).withSource(exp, overwrite = true)
        }
    }

    if (tripples.nonEmpty) {

      val rhsContainTerms = tripples map { case (decl, innerRegion, innerArgs) =>
        vpr.AnySetContains(
          decl.localVar,
          interferenceSetFunctions.application(innerRegion, innerArgs)
        )()
      }

      val triggerTerms = tripples map { case (decl, innerRegion, innerArgs) =>
        interferenceSetFunctions.triggerApplication(innerRegion, innerArgs :+ decl.localVar)
      }

      val decls = tripples map { case (decl, _, _) => decl }

      val lhsContainTerm =
        vpr.AnySetContains(
          state,
          interferenceSetFunctions.application(region, args)
        )()

      val body = vpr.EqCmp(lhsContainTerm, viper.silicon.utils.ast.BigAnd(rhsContainTerms))()

      val tranformStmt =
        vpr.Inhale(
          vpr.Forall(
            decls,
            Vector(vpr.Trigger(triggerTerms)()),
            body
          )()
        )()

      val footprintHavocs = tripples map { case (decl, innerRegion, innerArgs) =>
        val wrapper = singleWrapper(innerArgs)
          interferenceSetFunctions.havoc(innerRegion)(wrapper)
      }

      // TODO maybe add contains assertions for better trigger usage

      vpr.Seqn(
        footprintHavocs :+
          tranformStmt,
        Vector.empty
      )()

    } else {
      ViperAstUtils.Seqn()(info = vpr.SimpleInfo(Vector("", "no interference context translation needed", "")))
    }
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
      interferenceSetFunctions.application(region, regionArgs)
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
      val interferenceFootprintAccess = null

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

  def nextStateContainedInInference(region: PRegion): Constraint = Constraint( args => target =>
    TranslatorUtils.BetterQuantifierWrapper.UnitWrapperExt(
      vpr.AnySetContains(
        target,
        interferenceSetFunctions.application(region, args)
      )()
    )
  )

  def containsAllPossibleNextStatesConstraint(region: PRegion, possibleNextStateConstraint: Constraint): Constraint = {
    def constrain(args: Vector[Exp])(target: Exp): TranslatorUtils.BetterQuantifierWrapper.WrapperExt = {

      val varName = "$_m" // TODO: naming convention
      val varType = regionStateFunction(region).typ
      val varDecl = vpr.LocalVarDecl(varName, varType)()
      val variable = varDecl.localVar

      val regionArgs = args

      /* m in X(xs)*/
      val varInInterference =
        vpr.AnySetContains(
          variable,
          target
        )()

      val varIsPossibleNextState: TranslatorUtils.BetterQuantifierWrapper.WrapperExt =
        possibleNextStateConstraint.constrain(args)(variable)

      /* m in X(xs) <==> preState(xs) ~> m */
      varIsPossibleNextState.combine(e =>
        TranslatorUtils.BetterQuantifierWrapper.QuantWrapperExt(
          Vector(varDecl),
          vpr.EqCmp(varInInterference, e)()
        )
      )
    }

    Constraint(constrain, possibleNextStateConstraint.skolemization)
  }

}
