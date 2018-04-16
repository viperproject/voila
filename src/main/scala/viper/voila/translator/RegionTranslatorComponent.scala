/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.breakOut
import scala.collection.mutable
import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.collect
import sourcecode.Name.Machine
import viper.silver.ast.Exp
import viper.voila.backends.ViperAstUtils
import viper.voila.frontend._
import viper.voila.reporting.InsufficientGuardPermissionError
import viper.silver.ast.utility.Rewriter.Traverse
import viper.silver.{ast => vpr}
import viper.silver.verifier.{reasons => vprrea}

trait RegionTranslatorComponent { this: PProgramToViperTranslator =>
  private val regionStateFunctionCache =
    mutable.Map.empty[PRegion, vpr.Function]

  private val guardPredicateCache =
    mutable.Map.empty[(PGuardDecl, PRegion), vpr.Predicate]

  protected val collectedActionSkolemizationFunctionFootprints =
    /* Maps regions to corresponding skolemization function footprints */
    mutable.Map.empty[String, vpr.Predicate]

  protected val collectedActionSkolemizationFunctions =
    /* Maps pairs of region and variable names to corresponding skolemization functions */
    mutable.Map.empty[(String, String), vpr.Function]

  def regionPredicateAccess(region: PRegion,
                            arguments: Vector[vpr.Exp],
                            permissions: vpr.Exp = vpr.FullPerm()())
                           : vpr.PredicateAccessPredicate =
  {
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


  def actionSkolemizationFunctionFootprintName(regionName: String): String =
    s"${regionName}_sk_fp"

  def collectActionSkolemizationFunctionFootprint(region: PRegion): vpr.Predicate = {
    val footprintPredicate =
      vpr.Predicate(
        name = actionSkolemizationFunctionFootprintName(region.id.name),
        formalArgs = Vector.empty,
        body = None
      )()

    collectedActionSkolemizationFunctionFootprints += region.id.name -> footprintPredicate

    footprintPredicate
  }

  def actionSkolemizationFunctionFootprintAccess(regionName: String)
                                                : vpr.PredicateAccessPredicate = {

    vpr.PredicateAccessPredicate(
      vpr.PredicateAccess(
        args = Vector.empty,
        predicateName = actionSkolemizationFunctionFootprintName(regionName)
      )(),
      vpr.FullPerm()()
    )()
  }

  def actionSkolemizationFunctionName(regionName: String, variableName: String): String =
    s"${regionName}_sk_$variableName"

  def collectActionSkolemizationFunctions(region: PRegion): Vector[vpr.Function] = {
    val binders: Vector[PNamedBinder] = region.actions.flatMap(_.binders).distinct

    val vprSkolemizationFunctions =
      binders map (binder => {
        val vprFormalArguments = region.formalInArgs map translate
        val vprFootprint = actionSkolemizationFunctionFootprintAccess(region.id.name)

        val vprSkolemizationFunction =
          vpr.Function(
            name = actionSkolemizationFunctionName(region.id.name, binder.id.name),
            formalArgs = vprFormalArguments,
            typ = translate(semanticAnalyser.typeOfLogicalVariable(binder)),
            pres = Vector(vprFootprint),
            posts = Vector.empty,
            decs = None,
            body = None
          )()

        collectedActionSkolemizationFunctions +=
          (region.id.name, binder.id.name) -> vprSkolemizationFunction

        vprSkolemizationFunction
      })

    vprSkolemizationFunctions
  }

  def guardPredicateName(guard: PGuardDecl, region: PRegion): String =
    s"${region.id.name}_${guard.id.name}"

  def extractGuardAndRegionNameFromGuardPredicateName(guardPredicateName: String)
                                                     : (String, String) = {

    val splittedName = guardPredicateName.split("_")

    (splittedName(0), splittedName(1))
  }


  def guardPredicate(guard: PGuardDecl, region: PRegion): vpr.Predicate = {
    guardPredicateCache.getOrElseUpdate(
      (guard, region),
      {
        val regionIdArgument = vpr.LocalVarDecl("$r", translate(PRegionIdType()))()
        val otherArguments = guard.formalArguments map translate

        (guard.modifier,otherArguments) match {
          case (_: PUniqueGuard | _: PDuplicableGuard, args) =>
            vpr.Predicate(
              name = guardPredicateName(guard, region),
              formalArgs = regionIdArgument +: args,
              body = None
            )()

          case (_: PDivisibleGuard, perm +: args) =>
            vpr.Predicate(
              name = guardPredicateName(guard, region),
              formalArgs = regionIdArgument +: args,
              body = None
            )()
        }
      }
    )
  }

  def guardTriggerFunctionName(guard: PGuardDecl, region: PRegion): String =
    s"${guardPredicateName(guard, region)}_T"

  def guardTriggerFunction(guard: PGuardDecl, region: PRegion): Option[vpr.DomainFunc] = {
    val guardPred = guardPredicate(guard, region)

    if (guardPred.formalArgs.isEmpty) {
      None
    } else {
      Some(
        vpr.DomainFunc(
          name = guardTriggerFunctionName(guard, region),
          formalArgs = guardPred.formalArgs,
          typ = vpr.Bool
        )(domainName = regionStateTriggerFunctionsDomainName)
      )
    }
  }

  def guardTriggerFunction(guardPredicateName: String): Option[vpr.DomainFunc] = {
    val (guardName, regionName) = extractGuardAndRegionNameFromGuardPredicateName(guardPredicateName)
    val region = tree.root.regions.find(_.id.name == regionName).get
    val guard = region.guards.find(_.id.name == guardName).get

    guardTriggerFunction(guard, region)
  }

  def guardTriggerFunctionApplication(guardPredicateApplication: vpr.PredicateAccess)
                                     : Option[vpr.DomainFuncApp] =
    guardTriggerFunction(guardPredicateApplication.predicateName) map {
      guardTriggerFunc =>
        vpr.DomainFuncApp(
          func = guardTriggerFunc,
          args = guardPredicateApplication.args,
          typVarMap = Map.empty
        )()
    }

  def guardTriggerFunctionApplication(guard: PGuardDecl, args: Vector[vpr.Exp], region: PRegion)
                                     : Option[vpr.DomainFuncApp] =
    guardTriggerFunction(guard, region) map {
      guardTriggerFunc =>
        vpr.DomainFuncApp(
          func = guardTriggerFunc,
          args = args,
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
     ++ region.guards.flatMap(guard => guardTriggerFunction(guard, region))
     ++ Vector(skolemizationFunctionFootprint)
     ++ skolemizationFunctions
     ++ region.formalOutArgs.indices.map(regionOutArgumentFunction(region, _))
     ++ Vector(
          regionPredicate,
          regionStateFunction(region),
          regionStateTriggerFunction(region)))
  }

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
                                           : (PRegion, Vector[vpr.Exp], Vector[vpr.EqCmp]) = {

    val (region, inArgs, outArgsAndState) = getRegionPredicateDetails(predicateExp)

    val vprInArgs = inArgs map translate

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

    (region, vprInArgs, vprOutConstraints)
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

  def translate(guardExp: PRegionedGuardExp): Exp = {
    semanticAnalyser.entity(guardExp.guard) match {
      case GuardEntity(guardDecl, region) =>
        val (guardPredicateAccess, guardPredicateAccessLoc) =
          translateUseOf(guardExp, guardDecl, region)

        errorBacktranslator.addReasonTransformer {
          case e: vprrea.InsufficientPermission if e causedBy guardPredicateAccessLoc =>
            InsufficientGuardPermissionError(guardExp)
        }

        guardPredicateAccess
    }
  }

  def translateUseOf(guardExp: PRegionedGuardExp, guardDecl: PGuardDecl, region: PRegion)
                    : (vpr.Exp, vpr.PredicateAccess) = {

    val vprGuardPredicate = guardPredicate(guardDecl, region)

    val translatedRegionId = translate(guardExp.regionId)

    /* acc(guard(r,args), perm) */
    def accessPredicate(args: Vector[vpr.Exp], perm: vpr.Exp): vpr.PredicateAccessPredicate =
      vpr.PredicateAccessPredicate(
        vpr.PredicateAccess(
          translatedRegionId +: args,
          vprGuardPredicate.name
        )().withSource(guardExp),
        perm
      )().withSource(guardExp)

    /* body && [guardT(args), true] */
    def triggerWrapper(args: Vector[vpr.Exp], body: vpr.Exp): vpr.Exp =
      vpr.And(
        body,
        vpr.InhaleExhaleExp(
          guardTriggerFunctionApplication(
            guardDecl,
            translatedRegionId +: args,
            region
          ).get,
          vpr.TrueLit()()
        )()
      )()


    guardExp.argument match {
      case PStandartGuardArg(args) =>
        constructFromModifier(
          guardDecl.modifier,
          args map translate
        ){ case (predArgs, perm) =>
          val body = accessPredicate(predArgs, perm)

          if (predArgs.isEmpty) {
            (body, body.loc)
          } else {
            (triggerWrapper(predArgs, body), body.loc)
          }
        }

      case PSetGuardArg(set) =>
        val (conditional, decls) = extractGuardSetArgConditional(set)

        constructFromModifier(
          guardDecl.modifier,
          decls map (_.localVar)
        ){ case (predArgs, perm) =>
          val body = accessPredicate(predArgs, perm)

          val rhs = if (predArgs.isEmpty) {
            body
          } else {
            triggerWrapper(predArgs, body)
          }

          val trigger = guardTriggerFunctionApplication(
            guardDecl,
            translatedRegionId +: predArgs,
            region
          ).get

          val total = vpr.Forall(
            decls,
            Seq(vpr.Trigger(Seq(trigger))()),
            vpr.Implies(
              conditional,
              rhs
            )()
          )()

          (total, body.loc)
        }
    }
  }

  private def extractGuardSetArgConditional(set: PExpression): (vpr.Exp, Vector[vpr.LocalVarDecl]) = {
    val vipElemTypes = semanticAnalyser.typ(set) match {
      case PTupleType(elementTypes) =>
        elementTypes map translate

      case other =>
        sys.error(s"${set.pretty} should be of type Tuple but is ${other}")
    }

    val decls = vipElemTypes.zipWithIndex map { case (typ, ix) =>
      vpr.LocalVarDecl(s"$$a_$ix", typ)()
    }

    val conditional = vpr.DomainFuncApp(
      func = preamble.tuples.tuple(decls.length),
      args = decls map (_.localVar),
      typVarMap = preamble.tuples.typeVarMap(vipElemTypes)
    )()

    (conditional, decls)
  }

  private def constructFromModifier[A](modifier: PModifier,
                                       expArgs: Vector[vpr.Exp],
                                       dfltPerm: vpr.Exp = vpr.FullPerm()())
                                      (constructor: (Vector[vpr.Exp], vpr.Exp) => A): A = {

    (modifier, expArgs) match {
      case (_: PUniqueGuard | _:PDuplicableGuard, args) =>
        constructor(args, dfltPerm)

      case (_: PDivisibleGuard, perm +: args) =>
        constructor(args, perm)
    }
  }

  private def generateCodeForStabilizingAllRegionInstances(
                region: PRegion,
                actionFilter: PAction => Boolean,
                preRegionState: Vector[vpr.Exp] => vpr.Exp,
                postRegionState: Vector[vpr.Exp] => vpr.Exp,
                prePermissions: vpr.Exp => vpr.Exp,
                stateTrigger: Vector[vpr.Exp] => vpr.Trigger)
               : vpr.Seqn = {

    /* Arguments as for region R */
    val vprRegionArgumentDecls: Vector[vpr.LocalVarDecl] = region.formalInArgs.map(translate)

    /* Arguments as for region R */
    val vprRegionArguments: Vector[vpr.LocalVar] = vprRegionArgumentDecls map (_.localVar)

    /* First element a_0 of region arguments as */
    val vprRegionId = vprRegionArguments.head

    /* R(as) */
    val vprRegionPredicateInstance =
      vpr.PredicateAccess(
        args = vprRegionArguments,
        predicateName = region.id.name
      )()


    /* π */
    val vprPreHavocRegionPermissions =
      prePermissions(vpr.CurrentPerm(vprRegionPredicateInstance)())

    /* Note: It is assumed that havocking a region R(as) should not affect the permission
     * amount. Hence, π is used everywhere, i.e. there is not dedicated post-havoc permission
     * amount in use.
     */

    /* acc(R(as), π) */
    val vprRegionAssertion =
      vpr.PredicateAccessPredicate(
        loc = vprRegionPredicateInstance,
        perm = vprPreHavocRegionPermissions
      )()

    /* R_state(as) */
    val vprPreRegionState = preRegionState(vprRegionArguments)

    /* R_state'(as) */
    val vprPostRegionState = postRegionState(vprRegionArguments)

    /* ∀ as · acc(R(as), π) */
    val vprQuantifiedRegionAssertion =
      vpr.Forall(
        variables = vprRegionArgumentDecls,
        triggers = Vector.empty, /* TODO: Picking triggers not yet possible due to Viper limitations */
        exp = vprRegionAssertion
      )()

    /* exhale ∀ as · acc(R(as), π) */
    val vprExhaleAllRegionInstances = vpr.Exhale(vprQuantifiedRegionAssertion)()

    /* inhale ∀ as · acc(R(as), π) */
    val vprInhaleAllRegionInstances = vpr.Inhale(vprQuantifiedRegionAssertion)()


    /* none < π */
    val vprIsRegionAccessible =
      vpr.PermLtCmp(
        vpr.NoPerm()(),
        vprPreHavocRegionPermissions
      )()

    /* R_state'(as) == R_state(as) */
    val vprStateUnchanged =
      vpr.EqCmp(
        vprPostRegionState,
        vprPreRegionState
      )()

    val vprStateConstraintsFromActions: vpr.Exp =
      viper.silicon.utils.ast.BigOr(
        region.actions map (action =>
          stateConstraintsFromAction(
            action,
            vprPreRegionState,
            vprPostRegionState,
            assembleCheckIfEnvironmentMayHoldActionGuard(region, vprRegionId, action))))

    val vprStateConstraintsFromAtomicityContext = {
      /* none < perm(a_0 |=> <D>) */
      val vprDiamondHeld =
        vpr.PermLtCmp(
          vpr.NoPerm()(),
          vpr.CurrentPerm(diamondAccess(vprRegionId).loc)()
        )()

      /* X(as) */
      val vprAtomicityContext =
        vpr.DomainFuncApp(
          atomicityContextFunction(region),
          vprRegionArguments,
          Map.empty[vpr.TypeVar, vpr.Type]
        )()

      vpr.Implies(
        vprDiamondHeld,
        vpr.AnySetContains(
          vprPostRegionState,
          vprAtomicityContext
        )()
      )()
    }


    val vprConstrainRegionState =
      vpr.And(
        vprStateConstraintsFromAtomicityContext,
        vpr.Or(
          vprStateUnchanged,
          vprStateConstraintsFromActions
        )()
      )()

    val vprConstrainStateIfRegionAccessible =
      vpr.Implies(
        vprIsRegionAccessible,
        vprConstrainRegionState
      )()

    val vprConstrainStateOfAllAccessibleRegions =
      vpr.Inhale(
        vpr.Forall(
          variables = vprRegionArgumentDecls,
          triggers = Vector(stateTrigger(vprRegionArguments)),
          exp = vprConstrainStateIfRegionAccessible
        )()
      )()

    var vprPreliminaryResult =
      vpr.Seqn(
        Vector(
          vprExhaleAllRegionInstances,
          vprInhaleAllRegionInstances,
          vprConstrainStateOfAllAccessibleRegions
        ),
        Vector.empty
      )()


    /* Skolemize action existentials */

    def substitute(v: vpr.LocalVar, qvars: Seq[vpr.LocalVar]): vpr.Exp = {
      vpr.FuncApp(
        collectedActionSkolemizationFunctions(region.id.name, v.name),
        qvars
      )()
    }

    val vprSkolemizedResult =
      ViperAstUtils.skolemize(vprPreliminaryResult, substitute)

    /* TODO: Ideally, method substitute records which skolemization functions are in use, and then
     *       only their footprints are havocked. See also issue #47.
     */

    /* acc(R_sk_fp()) */
    val vprActionSkolemizationFunctionFootprintAccess =
      actionSkolemizationFunctionFootprintAccess(region.id.name)

    /* exhale acc(R_sk_fp()) */
    val vprExhaleActionSkolemizationFunctionFootprint =
      vpr.Exhale(vprActionSkolemizationFunctionFootprintAccess)()

    /* inhale acc(R_sk_fp()) */
    val vprInhaleActionSkolemizationFunctionFootprint =
      vpr.Inhale(vprActionSkolemizationFunctionFootprintAccess)()

    vprPreliminaryResult =
      vprSkolemizedResult.copy(
        ss =
          Vector(vprExhaleActionSkolemizationFunctionFootprint,
                 vprInhaleActionSkolemizationFunctionFootprint) ++
          vprSkolemizedResult.ss
      )(vprSkolemizedResult.pos, vprSkolemizedResult.info, vprSkolemizedResult.errT)


    ViperAstUtils.sanitizeBoundVariableNames(vprPreliminaryResult)
  }

  def stabilizeAllRegionInstances(region: PRegion, preHavocLabel: vpr.Label): vpr.Seqn = {
    val actionFilter: PAction => Boolean =
      _ => true

    val postRegionState =
      (args: Vector[vpr.Exp]) => vpr.FuncApp(regionStateFunction(region), args)()

    val preRegionState =
      (args: Vector[vpr.Exp]) => vpr.LabelledOld(postRegionState(args), preHavocLabel.name)()

    val prePermissions =
      (exp: vpr.Exp) => vpr.LabelledOld(exp, preHavocLabel.name)()

    val stateTrigger =
      (args: Vector[vpr.Exp]) =>
        vpr.Trigger(Vector(regionStateTriggerFunctionApplication(postRegionState(args))))()

    generateCodeForStabilizingAllRegionInstances(
      region,
      actionFilter,
      preRegionState,
      postRegionState,
      prePermissions,
      stateTrigger)
  }

  def stabilizeRegionInstance(region: PRegion,
                              vprRegionInArgs: Vector[vpr.Exp],
                              vprPreHavocLabel: vpr.Label)
                             : vpr.Seqn = {

    val vprHavocAllInstances = stabilizeAllRegionInstances(region, vprPreHavocLabel)

    /* R(as) */
    val vprRegionPredicateInstance =
      vpr.PredicateAccess(
        args = vprRegionInArgs,
        predicateName = region.id.name
      )()

    /* Note: The instantiation code is rather brittle since it makes the following assumptions:
     *   1. Each forall quantifies over region instance arguments 'as' of the given region and thus
     *      is to be instantiated
     *   2. Each perm(R(as)) is to be replaced with write
     */

    /* Note: Certain expressions in the resulting Viper AST could be simplified to potentially
     * improve performance, e.g. none < old[pre_havoc](write).
     */

    vprHavocAllInstances.transform(
      {
        case forall: vpr.Forall =>
          val substitutions: Map[vpr.LocalVar, vpr.Exp] =
            forall.variables.map(_.localVar).zip(vprRegionInArgs)(breakOut)

          forall.exp.replace(substitutions)

        case _: vpr.ForPerm =>
          sys.error("Unexpectedly found forperm quantifier while instantiating region havocking code")

        case vpr.CurrentPerm(`vprRegionPredicateInstance`) =>
          vpr.FullPerm()(): vpr.Node // TODO: Type ascription suppresses false IntelliJ type error
      },
      Traverse.TopDown)
  }

  def regionStateChangeAllowedByGuard(region: PRegion,
                                      vprRegionInArgs: Vector[vpr.Exp],
                                      guards: Vector[PRegionedGuardExp],
                                      vprFrom: vpr.Exp,
                                      vprTo: vpr.Exp)
                                     : vpr.Assert = {

    /* from == to */
    val vprUnchanged = vpr.EqCmp(vprFrom, vprTo)()


    /*
    val guardMap =
      new  mutable.HashMap[String, mutable.Set[Vector[PExpression]]]
      with mutable.MultiMap[String, Vector[PExpression]]

    guards foreach {guard => guardMap.addBinding(guard.guard.name, guard.arguments)}


*/
    // FIXME: Assumes, every guard kind only occurs once (in guards and action). Maybe automatically combine all guards of the same kind
    val guardMap = guards.map(g => g.guard.name -> g.argument).toMap

    def relevantAction(action: PAction): Boolean = {
      // FIXME: assumes globally unique guard name
      val actionKinds = action.guards map (_.guard.name)

      actionKinds forall (guardMap contains _)
    }

    val relevantActions = region.actions filter relevantAction

    val vprActionConstraints: Vector[vpr.Exp] =
      relevantActions.map(action => {

        val vprExistentialConstraint = stateConstraintsFromAction(
          action,
          vprFrom,
          vprTo,
          vpr.TrueLit()())

        var vprConjunctGuardCheck: vpr.Exp = vpr.TrueLit()()

        var vprConditionGuardCheck: vpr.Exp = vpr.TrueLit()()

        var conditionVars: Vector[vpr.LocalVarDecl] = Vector.empty

        action.guards foreach { case PBaseGuardExp(aGuardId, aGuardArg) =>

          val guardKind = semanticAnalyser.entity(aGuardId) match {
            case GuardEntity(guardDecl, `region`) => guardDecl
          }

          val guardArg = guardMap(aGuardId.name)

          (guardArg, aGuardArg) match {
            case (PStandartGuardArg(guardArgs), PStandartGuardArg(aGuardArgs)) =>
              (guardKind.modifier, guardArgs, aGuardArgs) match {
                case (_: PDivisibleGuard, r +: heldPerm +: _, requiredPerm +: _) =>
                  vprConjunctGuardCheck = vpr.And(
                    vprConjunctGuardCheck,
                    vpr.PermLeCmp(
                      translate(requiredPerm),
                      translate(heldPerm)
                    )()
                  )()

                case _ =>
              }
          }
        }

        val binderInstantiations: Map[String, vpr.Exp] =
          action.binders.map(binder =>
              if (AstUtils.isBoundVariable(action.from, binder)) {
                binder.id.name -> vprFrom
              } else if (AstUtils.isBoundVariable(action.to, binder)) {
                binder.id.name -> vprTo
              } else {
                val guardOption = action.guards find { _.argument match {
                  case PStandartGuardArg(args) =>
                    args.exists(AstUtils.isBoundVariable(_, binder))

                  case _ => false
                }}

                guardOption match {
                  case Some(PBaseGuardExp(guardId, PStandartGuardArg(guardArguments))) =>
                    /* The bound variable is a direct argument of the action guard G, i.e. the action
                     * guard is of the shape G(..., k, ...).
                     */

                    val argumentIndex = /* Index of k in G(..., k, ...) */
                      guardArguments.indexWhere(arg => AstUtils.isBoundVariable(arg, binder))

                    guardMap(guardId.name) match {
                      case PStandartGuardArg(args) =>
                        val vprArgument = /* Guard predicate is G(r, ..., k, ...) */
                          translate(args(argumentIndex))

                        binder.id.name -> vprArgument

                      case _ =>
                        sys.error(
                          s"The action at ${action.lineColumnPosition} does not belong to the class of "+
                          "currently supported actions. See issue #51 for further details.")
                    }

                  case _ =>
                    sys.error(
                      s"The action at ${action.lineColumnPosition} does not belong to the class of "+
                      "currently supported actions. See issue #51 for further details.")
                }
              }
          )(breakOut)

        val substitutes: Map[vpr.LocalVar, vpr.Exp] =
          vprExistentialConstraint.variables.map(v =>
            v.localVar -> binderInstantiations(v.name)
          )(breakOut)

        val actionConstraint = vprExistentialConstraint.exp.replace(substitutes)

        val bodyRhs = vpr.And(actionConstraint,vprConjunctGuardCheck)()

        val body = vpr.Implies(vprConditionGuardCheck, bodyRhs)()

        if (conditionVars.isEmpty) {
          body
        } else {
          // TODO: output forall
          ???
        }
      })

    val vprConstraint = viper.silicon.utils.ast.BigOr(vprUnchanged +: vprActionConstraints)

    vpr.Assert(
      /* The AST simplifier is invoked because the substitution of the bound action variables
       * will result in several trivially-true subexpressions of the shape
       * state(r, x) == state(r, x).
       */
      viper.silver.ast.utility.Simplifier.simplify(vprConstraint)
    )()
  }

  private def stateConstraintsFromAction(action: PAction,
                                         vprFrom: vpr.Exp,
                                         vprTo: vpr.Exp,
                                         vprGuardCheck: vpr.Exp)
                                        : vpr.Exists = {

    /* Let action be defined as follows:
     *   ?xs | c(xs) | G(g(xs)): e(xs) ~> e'(xs)
     */

    /* e(xs) == from */
    val vprFromWasPreHavocState =
      vpr.EqCmp(
        translate(action.from),
        vprFrom
      )()

    /* e'(xs) == to */
    val vprToIsNewState =
      vpr.EqCmp(
        translate(action.to),
        vprTo
      )()

    /* c(xs) */
    val vprCondition = translate(action.condition)

    /*  e(xs) == from ∧ e'(xs) == to ∧ c(x) ∧ guard_check */
    val vprExistentialBody =
      viper.silicon.utils.ast.BigAnd(
        Vector(
          vprFromWasPreHavocState,
          vprToIsNewState,
          vprCondition,
          vprGuardCheck))

    /* ∃ xs · body(xs) */
    vpr.Exists(
      action.binders map localVariableDeclaration,
      vprExistentialBody
    )()
  }

  private def assembleCheckIfEnvironmentMayHoldActionGuard(region: PRegion,
                                                           vprRegionId: vpr.Exp,
                                                           action: PAction)
  : vpr.Exp = viper.silicon.utils.ast.BigAnd(
    action.guards.map{case PBaseGuardExp(gid, gargs) =>
      assembleCheckIfEnvironmentMayHoldBaseActionGuard(region, vprRegionId, gid, gargs)
    }
  )

  private def assembleCheckIfEnvironmentMayHoldBaseActionGuard(region: PRegion,
                                                           vprRegionId: vpr.Exp,
                                                               guardId: PIdnUse,
                                                               guardArgument: PGuardArg)
  : vpr.Exp = semanticAnalyser.entity(guardId) match {
    case GuardEntity(guardDecl, `region`) =>
      guardArgument match {
        case PStandartGuardArg(guardArguments) =>
          (guardDecl.modifier, guardArguments) match {
            case (_: PDuplicableGuard, args) =>
              vpr.TrueLit () ()

            case (_: PUniqueGuard, args) =>
              vpr.EqCmp (
                vpr.CurrentPerm (
                  vpr.PredicateAccess (
                    vprRegionId +: (args map translate),
                    guardPredicate (guardDecl, region).name
                  ) ()
                ) (),
                vpr.NoPerm () ()
              ) ()

            case (_: PDivisibleGuard, requiredPerm +: args) =>
              vpr.PermLeCmp (
                vpr.CurrentPerm (
                  vpr.PredicateAccess (
                    vprRegionId +: (args map translate),
                    guardPredicate (guardDecl, region).name
                  ) ()
                ) (),
                vpr.PermSub (
                  vpr.FullPerm () (),
                  translate (requiredPerm)
                ) ()
              ) ()
          }
      }

    case _ =>
      sys.error(
        s"Unexpectedly failed to find a declaration for the guard denoted by " +
        s"${guardId} (${guardId.position})")
  }
}


