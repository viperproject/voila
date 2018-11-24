/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.breakOut
import scala.collection.mutable
import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.collect
import viper.voila.frontend._
import viper.voila.reporting._
import viper.silver.{ast => vpr}
import viper.silver.verifier.{errors => vprerr}
import viper.voila.translator.TranslatorUtils.{BaseSelector, BasicManagerWithSimpleApplication}

trait RegionTranslatorComponent { this: PProgramToViperTranslator =>
  private val regionStateFunctionCache =
    mutable.Map.empty[PRegion, vpr.Function]

  protected var collectingFunctions: List[PRegion => Vector[vpr.Declaration]] = Nil

  def regionPredicateAccess(region: PRegion,
                            arguments: Vector[vpr.Exp],
                            permissions: vpr.Exp = vpr.FullPerm()())
                           : vpr.PredicateAccessPredicate = {

    vpr.PredicateAccessPredicate(
      loc = vpr.PredicateAccess(
                args = arguments,
                predicateName = region.id.name
            )(),
      perm = permissions
    )()
  }

  /* TODO: Unify/share code between regionOutArgumentXXX and regionStateFunction */

  def regionOutArgumentFunctionName(region: PRegion, index: Int): String =
    s"${region.id.name}_out$index"

  def regionOutArgumentFunction(region: PRegion, index: Int): vpr.Function = {
    assert(
      0 <= index && index < region.formalOutArgs.length + 1,
      s"Expected 0 <= index < ${region.formalOutArgs.length}, but got $index")

    if (index == region.formalOutArgs.length) {
      regionStateFunction(region)
    } else {
      val outArg = region.formalOutArgs(index)
      val formalRegionArgs = region.formalInArgs map translate
      val outType = translate(outArg.typ)

      /* acc(region(inArgs)) */
      val predicateAccess =
        regionPredicateAccess(
          region,
          formalRegionArgs.map(_.localVar))

      val collectOutArgumentBinders =
        collect[Vector, PNamedBinder] {
          case binder: PNamedBinder if binder.id == outArg.id => binder
        }

      val outArgBinder =
        collectOutArgumentBinders(region.interpretation) match {
          case Seq() =>
            sys.error(s"Region out-argument ${outArg.id.name} isn't bound in the region interpretation")
          case Seq(binder) =>
            binder
          case _=>
            sys.error(s"Region out-argument ${outArg.id.name} is bound multiple times in the region interpretation")
        }

      val body =
        vpr.Unfolding(
          acc = predicateAccess,
          body = translateUseOf(outArgBinder.id)
        )()

      vpr.Function(
        name = regionOutArgumentFunctionName(region, index),
        formalArgs = formalRegionArgs,
        typ = outType,
        pres = Vector(predicateAccess),
        posts = Vector.empty,
        decs = None,
        body = Some(body)
      )()
    }
  }

  def regionStateFunctionName(region: PRegion): String =
    s"${region.id.name}_state"

  def extractRegionNameFromStateFunctionName(stateFunctionName: String): String = {
    val pattern = "(.*)_state".r
    val pattern(regionName) = stateFunctionName

    regionName
  }

  def regionStateFunction(region: PRegion): vpr.Function = {
    regionStateFunctionCache.getOrElseUpdate(
      region,
      {
        val formalRegionArgs = region.formalInArgs map translate
        val regionStateType = translate(semanticAnalyser.typ(region.state))

        /* acc(region(inArgs)) */
        val predicateAccess =
          regionPredicateAccess(
            region,
            formalRegionArgs.map(_.localVar))

        val body =
          vpr.Unfolding(
            acc = predicateAccess,
            body = translate(region.state)
          )()

        val mentionTriggerFunction =
          vpr.InhaleExhaleExp(
            /* TODO: It would be much simpler to use the other DomainFuncApp constructor
             * (object DomainFuncApp, method apply), but that one requires passing a domain
             * function instance. Getting the latter would currently cause a call chain cycle since
             * regionStateTriggerFunction(region) calls back into regionStateFunction(region)
             * (i.e. into this method).
             */
            vpr.DomainFuncApp(
              funcname = regionStateTriggerFunctionName(region),
              args = formalRegionArgs map (_.localVar),
              typVarMap = Map.empty
            )(pos = vpr.NoPosition,
              info = vpr.NoInfo,
              typPassed = vpr.Bool,
              formalArgsPassed = formalRegionArgs,
              domainName = regionStateTriggerFunctionsDomainName,
              errT = vpr.NoTrafos),
            vpr.TrueLit()()
          )()

        vpr.Function(
          name = regionStateFunctionName(region),
          formalArgs = formalRegionArgs,
          typ = regionStateType,
          pres = Vector(predicateAccess),
          posts = Vector(mentionTriggerFunction),
          decs = None,
          body = Some(body)
        )()
      })
  }

  val regionStateTriggerFunctionsDomainName: String = "trigger_functions"

  val regionStateTriggerFunctionDomain: vpr.Domain = {
    vpr.Domain(
      name = regionStateTriggerFunctionsDomainName,
      functions = Vector.empty,
      axioms = Vector.empty,
      typVars = Vector.empty
    )()
  }

  def regionStateTriggerFunctionName(region: PRegion): String =
    s"${regionStateFunctionName(region)}_T"

  def regionStateTriggerFunction(region: PRegion): vpr.DomainFunc = {
    val regionFunction = regionStateFunction(region)

    vpr.DomainFunc(
      name = regionStateTriggerFunctionName(region),
      formalArgs = regionFunction.formalArgs,
      typ = vpr.Bool
    )(domainName = regionStateTriggerFunctionsDomainName)
  }

  def regionStateTriggerFunction(regionName: String): vpr.DomainFunc = {
    val region = tree.root.regions.find(_.id.name == regionName).get

    regionStateTriggerFunction(region)
  }

  def regionStateTriggerFunctionApplication(stateFunctionApplication: vpr.FuncApp)
                                           : vpr.DomainFuncApp = {

    val regionName = extractRegionNameFromStateFunctionName(stateFunctionApplication.funcname)

    vpr.DomainFuncApp(
      func = regionStateTriggerFunction(regionName),
      args = stateFunctionApplication.args,
      typVarMap = Map.empty
    )()
  }



  def translate(region: PRegion): Vector[vpr.Declaration] = {
    val regionPredicateName = region.id.name

    val formalRegionArgs = region.formalInArgs map translate

    /* predicate region(id, args) { interpretation } */
    val regionPredicate =
      vpr.Predicate(
        name = regionPredicateName,
        formalArgs = formalRegionArgs,
        body = Some(translate(region.interpretation))
      )()

    /* predicate region_G(r: RegionId) for each guard G */
    val guardPredicates =
      region.guards map (guard => guardPredicate(guard, region))

    val skolemizationFunctionFootprint = collectActionSkolemizationFunctionFootprint(region)
    val skolemizationFunctions = collectActionSkolemizationFunctions(region)

    (   guardPredicates
     ++ collectingFunctions.flatMap(_(region)).distinct
     ++ region.guards.flatMap(guard => guardTriggerFunction(guard, region))
     ++ region.guards.flatMap(guard => guardTriggerFunctionAxiom(guard, region))
     ++ Vector(skolemizationFunctionFootprint)
     ++ skolemizationFunctions
     ++ region.formalOutArgs.indices.map(regionOutArgumentFunction(region, _))
     ++ Vector(
          regionPredicate,
          regionStateFunction(region),
          regionStateTriggerFunction(region)))
  }

  def additionalRegionChecks(region: PRegion): Vector[vpr.Declaration] = {
    maybeRegionInterpretationStabilityCheck(region).toVector ++
    maybeRegionActionsTransitivityCheck(region)
    // maybeRegionActionIndividualTransitivityCheck(region)
  }

  def maybeRegionInterpretationStabilityCheck(region: PRegion): Option[vpr.Method] = {
    if (config.stableConditionsCheck()) {
      Some(regionInterpretationStabilityCheck(region))
    } else {
      None
    }
  }

  def regionInterpretationStabilityCheck(region: PRegion): vpr.Method = {
    val methodName = s"$$_${region.id.name}_interpretation_stability_check"

    val formalArgs = region.formalInArgs map translate

    val body = {
      val inhaleSkolemizationFunctionFootprints =
        vpr.Inhale(
          viper.silicon.utils.ast.BigAnd(
            /* TODO: Would benefit from an optimisation similar to issue #47 */
            tree.root.regions map (region =>
              actionSkolemizationFunctionFootprintAccess(region.id.name)))
        )()

      val initializeFootprints = initializingFunctions.flatMap(tree.root.regions map _)

      val interpretation = translate(region.interpretation)

      val inhaleInterpretation = vpr.Inhale(interpretation)().withSource(region.interpretation)

      /* TODO: Could be optimized to only havocking regions that occur inside region interpretation */
      val stabilizationCode = stabilizeAllInstances("check stability of region interpretation")

      val assertInterpretation = vpr.Assert(interpretation)().withSource(region.interpretation)

      errorBacktranslator.addErrorTransformer {
        case e: vprerr.AssertFailed if e causedBy assertInterpretation =>
          RegionInterpretationNotStableError(region)
      }

      vpr.Seqn(
        inhaleSkolemizationFunctionFootprints +:
        initializeFootprints ++:
        Vector(
          inhaleInterpretation,
          stabilizationCode,
          assertInterpretation
        ),
        Vector.empty
      )()
    }

    vpr.Method(
      name = methodName,
      formalArgs = formalArgs,
      formalReturns = Vector.empty,
      pres = Vector.empty,
      posts = Vector.empty,
      body = Some(body)
    )()
  }

  def maybeRegionActionIndividualTransitivityCheck(region: PRegion): Vector[vpr.Method] = {
    if(config.transitiveActionsCheck()) {
      region.actions.zipWithIndex.map { case (a,i) =>
        regionActionIndividualTransitivityCheck(region,a,i.toString)
      }
    } else {
      Vector.empty
    }
  }

  def maybeRegionActionsTransitivityCheck(region: PRegion): Vector[vpr.Method] = {
    if(config.transitiveActionsCheck()) {
      Vector(regionActionTransitivityCheck(region))
    } else {
      Vector.empty
    }
  }

  def regionActionTransitivityCheck(region: PRegion): vpr.Method = {
    val methodName = s"$$_${region.id.name}_action_transitivity_check"

    val guards = region.guards

    val guardIds = guards.map{_.id.name}

    val guardDecls = guards.map{g => g.modifier match {
      case _: PUniqueGuard | _: PDuplicableGuard =>
        g.formalArguments.length match {
          case 0 =>
            vpr.LocalVarDecl(g.id.name, vpr.Bool)()

          case 1 =>
            val elementType = translate(g.formalArguments.head.typ)
            vpr.LocalVarDecl(g.id.name, vpr.SetType(elementType))()

          case n =>
            val elementType =
              vpr.DomainType(
                preamble.tuples.domain(n),
                preamble.tuples.typeVarMap(g.formalArguments map (d => translate(d.typ)))
              )
            vpr.LocalVarDecl(g.id.name, vpr.SetType(elementType))()
        }

      case _: PDivisibleGuard =>
        vpr.LocalVarDecl(g.id.name, vpr.Perm)()
    }}

    val guardVarMap = guardIds.zip(guardDecls map (_.localVar)).toMap
    val guardModifierMap = guardIds.zip(guards map (_.modifier)).toMap

    val actionMaps: Map[Int, Map[String, TranslatedPGuardArg]] =
      region.actions.zipWithIndex.map { case (a,i) =>
        i -> groupGuards(a.guards)
      }(breakOut)

    def actionApplication(action: PAction,
                          index: Int,
                          postfix: String)
    : (Vector[vpr.LocalVarDecl], vpr.Exp, vpr.Exp, vpr.Exp, vpr.Exp) = {

      val initialDecls = action.binders map localVariableDeclaration
      val initialVars = initialDecls map (_.localVar)

      val formalDecls = initialDecls.map{v => vpr.LocalVarDecl(s"${v.name}_${index}_$postfix", v.typ)()}
      val vars = formalDecls map (_.localVar)

      val renaming = initialVars.zip(vars).toMap

      val condition = translate(action.condition).replace(renaming)
      val from = translate(action.from).replace(renaming)
      val to = translate(action.to).replace(renaming)

      val guards = actionMaps(index).toVector

      val guardConstraints = guards map { case (name, arg) => (guardModifierMap(name), arg) match {
        case (_: PUniqueGuard | _: PDuplicableGuard, TranslatedPStandartGuardArg(args, _)) =>
          args.length match {
            case 0 => guardVarMap(name)
            case _ => vpr.AnySetContains(tupleWrap(args), guardVarMap(name))()
          }

        case (_: PUniqueGuard | _: PDuplicableGuard, TranslatedPSetGuardArg(set)) =>
          vpr.AnySetSubset(set, guardVarMap(name))()

        case (_: PDivisibleGuard, TranslatedPStandartGuardArg(args, _)) =>
          vpr.GeCmp(args.head, guardVarMap(name))()

        case other @ (_: PDivisibleGuard, _: TranslatedPSetGuardArg) =>
          sys.error(s"Unexpectedly found $other")
      }}

      (formalDecls, condition, from, to, viper.silicon.utils.ast.BigAnd(guardConstraints).replace(renaming))
    }

    def allActionApplication(from: vpr.Exp, to: vpr.Exp, postfix: String)
                            : (Vector[vpr.LocalVarDecl], vpr.Exp) = {

      val (declss, constraints) = region.actions.zipWithIndex.map { case (a,i) =>
        val (decls, aCondition, aFrom, aTo, aGuardConstraint) = actionApplication(a, i, postfix)

        val constraint = viper.silicon.utils.ast.BigAnd(
          Vector(
            vpr.EqCmp(aFrom, from)(),
            vpr.EqCmp(aTo, to)(),
            aCondition,
            aGuardConstraint
          )
        )

        (decls, constraint)
      }.unzip

      (declss.flatten, viper.silicon.utils.ast.BigOr(constraints))
    }

    def allActionApplication2(from: vpr.Exp, to: vpr.Exp, postfix: String): vpr.Exp = {
      val constraints = region.actions.zipWithIndex.map { case (a,i) =>
        val (fromBound, notFromBound) = a.binders.partition(isBoundExpExtractableFromPoint(_, a.from))
        val (toBound, restBinders) = notFromBound.partition(isBoundExpExtractableFromPoint(_, a.to))

        val fromBoundRenaming = fromBound.map(
          b => localVariableDeclaration(b).localVar -> extractBoundExpFromPoint(b, a.from, from).get
        )(breakOut)

        val toBoundRenaming = toBound.map(
          b => localVariableDeclaration(b).localVar -> extractBoundExpFromPoint(b, a.to, to).get
        )(breakOut)

        val initialDecls = restBinders map localVariableDeclaration
        val initialVars = initialDecls map (_.localVar)

        val formalDecls = initialDecls.map{v => vpr.LocalVarDecl(s"${v.name}_${i}_$postfix", v.typ)()}
        val vars = formalDecls map (_.localVar)

        val renaming = initialVars.zip(vars).toMap ++ fromBoundRenaming ++ toBoundRenaming

        val aCondition = translate(a.condition).replace(renaming)
        val aFrom = translate(a.from).replace(renaming)
        val aTo = translate(a.to).replace(renaming)

        val guards = actionMaps(i).toVector

        val aGuardConstraints = guards map { case (name, arg) =>
          (guardModifierMap(name), arg) match {
            case (_: PUniqueGuard | _: PDuplicableGuard, TranslatedPStandartGuardArg(args, _)) =>
              args.length match {
                case 0 => guardVarMap(name)
                case _ => vpr.AnySetContains(tupleWrap(args), guardVarMap(name))()
              }

            case (_: PUniqueGuard | _: PDuplicableGuard, TranslatedPSetGuardArg(set)) =>
              vpr.AnySetSubset(set, guardVarMap(name))()

            case (_: PDivisibleGuard, TranslatedPStandartGuardArg(args, _)) =>
              vpr.GeCmp(args.head, guardVarMap(name))()

            case (_: PDivisibleGuard, TranslatedPSetGuardArg(_)) => ???
          }
        }

        val aGuardConstraint = viper.silicon.utils.ast.BigAnd(aGuardConstraints).replace(renaming)

        val constraint = viper.silicon.utils.ast.BigAnd(
          Vector(
            vpr.EqCmp(aFrom, from)(),
            vpr.EqCmp(aTo, to)(),
            aCondition,
            aGuardConstraint
          )
        )

        if (formalDecls.isEmpty) {
          constraint
        } else {
          vpr.Exists(
            formalDecls,
            constraint
          )()
        }
      }

      viper.silicon.utils.ast.BigOr(constraints)
    }

    val stateType = translate(semanticAnalyser.typ(region.state))
    val aStateDecl = vpr.LocalVarDecl("aState", stateType)()
    val bStateDecl = vpr.LocalVarDecl("bState", stateType)()
    val cStateDecl = vpr.LocalVarDecl("cState", stateType)()

    val (xDecls, xConstraint) = allActionApplication(aStateDecl.localVar, bStateDecl.localVar, "x")
    val (yDecls, yConstraint) = allActionApplication(bStateDecl.localVar, cStateDecl.localVar, "y")
    val zConstraint = allActionApplication2(aStateDecl.localVar, cStateDecl.localVar, "z")

    val body = {
      val xInhale = vpr.Inhale(xConstraint)()
      val yInhale = vpr.Inhale(yConstraint)()

      val zAssert = vpr.Assert(zConstraint)()

      errorBacktranslator.addErrorTransformer {
        case e: vprerr.AssertFailed if e causedBy zAssert =>
          RegionActionsNotTransitiveError(region)
      }

      vpr.Seqn(
        Vector(
          xInhale,
          yInhale,
          zAssert
        ),
        guardDecls ++ xDecls ++ yDecls ++ Vector(aStateDecl, bStateDecl, cStateDecl)
      )()
    }

    vpr.Method(
      name = methodName,
      formalArgs = Vector.empty,
      formalReturns = Vector.empty,
      pres = Vector.empty,
      posts = Vector.empty,
      body = Some(body)
    )()
  }

  def regionActionIndividualTransitivityCheck(region: PRegion, action: PAction, actionName: String)
                                             : vpr.Method = {

    val methodName = s"$$_${region.id.name}_${actionName}_action_transitivity_check"

    val (guardBinder, stateBinder) = action.binders partition { binder =>
      action.guards.exists{ _.argument match {
        case PStandartGuardArg(args) =>
          args.exists(isBoundExpExtractableFromPoint(binder, _))

        case _ => false
      }}
    }

    val guardDecls = guardBinder map localVariableDeclaration

    val initialStateDecls = stateBinder map localVariableDeclaration
    val initialStateVars = initialStateDecls map (_.localVar)

    def actionApplication(postfix: String): (Vector[vpr.LocalVarDecl], vpr.Exp, vpr.Exp, vpr.Exp) = {
      val formalArgs = initialStateDecls map {v => vpr.LocalVarDecl(s"${v.name}_$postfix", v.typ)()}
      val vars = formalArgs map (_.localVar)

      val renaming = initialStateVars.zip(vars).toMap

      val condition = translate(action.condition).replace(renaming)
      val from = translate(action.from).replace(renaming)
      val to = translate(action.to).replace(renaming)

      (formalArgs, condition, from, to)
    }

    val (aDecls, aCond, aFrom, aTo) = actionApplication("a")
    val (bDecls, bCond, bFrom, bTo) = actionApplication("b")
    val (cDecls, cCond, cFrom, cTo) = actionApplication("c")

    val body = {
      val assumptions =
        viper.silicon.utils.ast.BigAnd(Vector(
          aCond, bCond, vpr.EqCmp(aTo, bFrom)(), vpr.EqCmp(aFrom, cFrom)(), vpr.EqCmp(bTo, cTo)()
        ))

      val transitivityAssertion = vpr.Assert(cCond)()

      errorBacktranslator.addErrorTransformer {
        case e: vprerr.AssertFailed if e causedBy transitivityAssertion =>
          ActionNotTransitiveError(action)
      }

      vpr.Seqn(
        Vector(
          vpr.Inhale(assumptions)(),
          transitivityAssertion
        ),
        guardDecls ++ aDecls ++ bDecls ++ cDecls
      )()
    }

    vpr.Method(
      name = methodName,
      formalArgs = Vector.empty,
      formalReturns = Vector.empty,
      pres = Vector.empty,
      posts = Vector.empty,
      body = Some(body)
    )()
  }

  def extractBoundRegionInstance(id: PIdnUse)
                                : Option[(PRegion, Vector[PExpression], Vector[PExpression])] = {

    semanticAnalyser.entity(id) match {
      case entity: LogicalVariableEntity =>

        val binder = entity.declaration

        semanticAnalyser.boundBy(binder) match {
          case predicateExp@PPredicateExp(_, innerArgs) if innerArgs.last eq binder =>
            Some(getRegionPredicateDetails(predicateExp))

          case PInterferenceClause(`binder`, _, regId) =>
            Some(getRegionPredicateDetails(semanticAnalyser.usedWithRegionPredicate(regId)))

          case _ => None
        }

      case _ => None
    }
  }

  def extractRegionInstance(pred: PPredicateExp)
                           : Option[(PRegion, Vector[PExpression], Vector[PExpression])] = {

    if (extractableRegionInstance(pred)) {
      Some(getRegionPredicateDetails(pred))
    } else {
      None
    }
  }

  def extractableRegionInstance(pred: PPredicateExp): Boolean =
    semanticAnalyser.entity(pred.predicate).isInstanceOf[RegionEntity]

  def getRegionPredicateDetails(predicateExp: PPredicateExp)
                               : (PRegion, Vector[PExpression], Vector[PExpression]) = {

    val region =
      semanticAnalyser.entity(predicateExp.predicate)
                      .asInstanceOf[RegionEntity]
                      .declaration

    val (inArgs, outArgsAndState) =
      predicateExp.arguments.splitAt(region.formalInArgs.length)

    (region, inArgs, outArgsAndState)
  }

  def getAndTranslateRegionPredicateDetails(predicateExp: PPredicateExp)
                                           : (PRegion, Vector[vpr.Exp], Vector[vpr.Exp], Vector[vpr.Exp]) = {

    val (region, inArgs, outArgsAndState) = getRegionPredicateDetails(predicateExp)

    val vprInArgs = inArgs map translate

    val vprInArgConstraints = {
      Vector(
        /* levels are always positive */
        vpr.GeCmp(vprInArgs(1), vpr.IntLit(0)())()
      )
    }

    val vprOutConstraints =
      outArgsAndState.zipWithIndex.flatMap {
        case (_: PLogicalVariableBinder, _) =>
          None
        case (exp, idx) =>
          val vprOutValue =
            vpr.FuncApp(
              regionOutArgumentFunction(region, idx),
              vprInArgs
            )()

          val constraint =
            vpr.EqCmp(
              vprOutValue,
              translate(exp)
            )()

          Some(constraint)
      }

    (region, vprInArgs, vprInArgConstraints, vprOutConstraints)
  }

  def regionState(predicateExp: PPredicateExp): vpr.FuncApp = {
    val (region, regionArguments, _) = getRegionPredicateDetails(predicateExp)

    regionState(region, regionArguments)
  }

  def regionState(region: PRegion, regionArguments: Vector[PExpression]): vpr.FuncApp = {
    val vprRegionArguments = regionArguments map translate

    vpr.FuncApp(
      regionStateFunction(region),
      vprRegionArguments)()
  }

  trait RegionManager[M <: vpr.Declaration, A <: vpr.Exp]
      extends BasicManagerWithSimpleApplication[PRegion, M, A] { this: BaseSelector[PRegion] =>

    override def idToName(id: PRegion): String = id.id.name

    override def getID(objName: String): PRegion =
      tree.root.regions.find(_.id.name == objName).get

    def collectMember(obj: PRegion): Vector[vpr.Declaration] =
      collectMember(TranslatorUtils.ManagedObject(obj, obj.formalInArgs map translate))

    if (this.isInstanceOf[TranslatorUtils.FrontSelector[PRegion]]) {
      collectingFunctions ::= (collectMember(_: PRegion)) /* TODO: not sure if this is safe */
    }

    this match {
      case self: RegionManager[M, A] with TranslatorUtils.FootprintManager[PRegion] =>
        initializingFunctions ::= (self.initialize(_: PRegion))
      case _ => /* Nothing to do */
    }
  }
}
