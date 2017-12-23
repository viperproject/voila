/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.mutable
import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.collect
import viper.voila.frontend._
import viper.voila.reporting.{InsufficientGuardPermissionError, InsufficientRegionPermissionError, RegionStateError}
import viper.silver.{ast => vpr}
import viper.silver.verifier.{reasons => vprrea}

trait RegionTranslatorComponent { this: PProgramToViperTranslator =>
  private val regionStateFunctionCache =
    mutable.Map.empty[PRegion, vpr.Function]

  private val guardTransitiveClosureFunctionCache =
    mutable.Map.empty[(PGuardDecl, PRegion), vpr.Function]

  private val guardPotentiallyHeldFunctionCache =
    mutable.Map.empty[(PGuardDecl, PRegion), vpr.Function]

  private val guardPredicateCache =
    mutable.Map.empty[(PGuardDecl, PRegion), vpr.Predicate]

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
        collect[Vector, PLogicalVariableBinder] {
          case binder: PLogicalVariableBinder if binder.id == outArg.id => binder
        }

      val outArgBinder =
        collectOutArgumentBinders(region.interpretation) match {
          case Seq() =>
            sys.error(s"Region out-argument ${outArg.id.name} isn't bound in the region interpretation")
          case Seq(binder) =>
            binder
          case other =>
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

  def guardPotentiallyHeldFunctionName(guard: PGuardDecl, region: PRegion): String =
    s"${region.id.name}_${guard.id.name}_potentiallyHeldByEnvironment"

  def guardPotentiallyHeldFunction(guard: PGuardDecl, region: PRegion): vpr.Function = {
    guardPotentiallyHeldFunctionCache.getOrElseUpdate(
      (guard, region),
      {
        val formalArgs =
          Vector(
            vpr.LocalVarDecl("$r", translate(PRegionIdType()))(),
            vpr.LocalVarDecl("$p", vpr.Perm)())

        val body =
          guard.modifier match {
            case PUniqueGuard() => vpr.EqCmp(formalArgs(1).localVar, vpr.NoPerm()())()
            case PDuplicableGuard() => vpr.TrueLit()()
          }

        vpr.Function(
          name = guardPotentiallyHeldFunctionName(guard, region),
          formalArgs = formalArgs,
          typ = vpr.Bool,
          pres = Vector.empty,
          posts = Vector.empty,
          decs = None,
          body = Some(body)
        )()
      })
  }

  def guardTransitiveClosureFunctionName(guard: PGuardDecl, region: PRegion): String =
    s"${region.id.name}_${guard.id.name}_transitiveClosure"

  def guardTransitiveClosureFunction(guard: PGuardDecl, region: PRegion): vpr.Function = {
    guardTransitiveClosureFunctionCache.getOrElseUpdate(
      (guard, region),
      {
        val regionType = translate(semanticAnalyser.typ(region.state))

        val formalArgs =
          Vector(
            vpr.LocalVarDecl("$r", translate(PRegionIdType()))(),
            vpr.LocalVarDecl("$from", regionType)())

        val body = {
          val actions = region.actions.filter(_.guard.name == guard.id.name)

          val vprFrom = formalArgs(1).localVar
          val vprFromSet = vpr.ExplicitSet(Vector(vprFrom))()

          /* TODO: Account for non-exclusive action constraints, e.g.
           *         G: ?n if 0 < n  ~~> Set(...)
           *         G: ?n if n < 10 ~~> Set(...)
           */
          actions
            .foldLeft[vpr.Exp](vprFromSet)((acc, action) => {
              action match {
                case PAction1(_, from, to) =>
                  /* Source: e ~> e'
                   * Encode: from == e ? e' : Set(from)
                   */
                  vpr.CondExp(
                    cond = vpr.EqCmp(vprFrom, translate(from))(),
                    thn = translate(to),
                    els = acc
                  )()

                case PAction2(_, from, to) =>
                  /* Source: ?x ~> e(x)
                   * Encode: e(from)
                   */
                  translate(to).transform {
                    case vpr.LocalVar(from.id.name) => vprFrom
                      /* TODO: Fragile, relies on 'x' being translated to 'x' */
                  }

                case PAction3(_, qvar, constraint, to) =>
                  /* Source: ?x if p(x) ~> Set(?y | q(x, y))
                   * Encode: p(from) ? setcomprehension_i(from) : Set(from)
                   */

                  vpr.CondExp(
                    cond = translate(constraint),
                    thn = translate(to),
                    els = acc
                  )().transform {
                    case vpr.LocalVar(qvar.id.name) => vprFrom
                      /* TODO: Fragile, relies on 'x' being translated to 'x' */
                  }
              }
            })
        }

        vpr.Function(
          name = guardTransitiveClosureFunctionName(guard, region),
          formalArgs = formalArgs,
          typ = vpr.SetType(regionType),
          pres = Vector.empty,
          posts = Vector.empty,
          decs = None,
          body = Some(body)
        )()
      })
  }

  def guardPredicateName(guard: PGuardDecl, region: PRegion): String =
    s"${region.id.name}_${guard.id.name}"

  def guardPredicate(guard: PGuardDecl, region: PRegion): vpr.Predicate = {
    guardPredicateCache.getOrElseUpdate(
      (guard, region),
      vpr.Predicate(
        name = guardPredicateName(guard, region),
        formalArgs = Vector(vpr.LocalVarDecl("$r", translate(PRegionIdType()))()),
        body = None
      )()
    )
  }

  def translate(region: PRegion): Vector[vpr.Declaration] = {
    val regionPredicateName = region.id.name

    val formalRegionArgs = region.formalInArgs map translate
    val formalRegionId = formalRegionArgs.head

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

    /* function region_G_potentiallyHeldByEnvironment(r: RegionId, p: Perm)
     *   {...}
     * for each guard G
     */
    val potentiallyHeldFunctions =
      region.guards map (guard => guardPotentiallyHeldFunction(guard, region))

    val transitiveClosureFunctions =
      region.guards map (guard => guardTransitiveClosureFunction(guard, region))

    (   guardPredicates
     ++ potentiallyHeldFunctions
     ++ transitiveClosureFunctions
     ++ region.formalOutArgs.indices.map(regionOutArgumentFunction(region, _))
     ++ Vector(
          regionPredicate,
          regionStateFunction(region),
          regionStateTriggerFunction(region)))
  }

  def translateUseOf(regionPredicate: PPredicateExp): (vpr.PredicateAccessPredicate, vpr.Exp) = {
    val (region, vprInArgs, vprOutArgConstraints) =
      getAndTranslateRegionPredicateDetails(regionPredicate)

//    val vprStateConstraint =
//      vprRegionStateArgument match {
//        case None | Some(Left(_: PLogicalVariableBinder)) => vpr.TrueLit()()
//        case Some(Right(vprStateArgument)) =>
//          val vprStateFunction = regionStateFunction(region)
//
//          vprStateArgument match {
//            case app: vpr.FuncApp if app.funcname == vprStateFunction.name =>
//              /* Avoid generation of redundant constraints of the shape state(a, x) == state(a, x).
//               * Should not be necessary in the long run.
//               */
//              vpr.TrueLit()()
//            case _ =>
//              vpr.EqCmp(
//                vpr.FuncApp(
//                  func = vprStateFunction,
//                  args = vprInArgs
//                )(),
//                vprStateArgument
//              )()
//          }
//      }

    val vprStateConstraint = viper.silicon.utils.ast.BigAnd(vprOutArgConstraints)

    val vprRegionPredicate =
      vpr.PredicateAccess(
        args = vprInArgs,
        predicateName = region.id.name
      )().withSource(regionPredicate)

    val vprRegionAccess =
      vpr.PredicateAccessPredicate(
        vprRegionPredicate,
        vpr.FullPerm()()
      )().withSource(regionPredicate)

    errorBacktranslator.addReasonTransformer {
      case e: vprrea.InsufficientPermission if e causedBy vprRegionPredicate =>
        InsufficientRegionPermissionError(regionPredicate)
      case e: vprrea.AssertionFalse if e causedBy vprStateConstraint =>
        RegionStateError(regionPredicate)
    }

    (vprRegionAccess, vprStateConstraint)
  }

  def getRegionPredicateDetails(predicateExp: PPredicateExp)
                               : (PRegion, Vector[PExpression], Vector[PExpression]) = {

    val region =
      semanticAnalyser.entity(predicateExp.predicate)
                      .asInstanceOf[RegionEntity]
                      .declaration

//    val (regionArguments, regionStateArgument) =
//      predicateExp.arguments.splitAt(region.formalInArgs.length) match {
//        case (args, Seq()) => (args, None)
//        case (args, Seq(binder: PLogicalVariableBinder)) => (args, Some(Left(binder)))
//        case (args, Seq(arg)) => (args, Some(Right(arg)))
//        case _ => sys.error(s"Unexpectedly many arguments: $predicateExp")
//      }
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
        case (_: PLogicalVariableBinder, _) => None
        case (_: PIrrelevantValue, _) => None
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

  def translate(guardExp: PGuardExp): vpr.PredicateAccessPredicate = {
    semanticAnalyser.entity(guardExp.guard) match {
      case GuardEntity(guardDecl, region) =>
        val guardPredicateAccess =
          translateUseOf(region, guardDecl, translateUseOf(guardExp.regionId), Some(guardExp))

        errorBacktranslator.addReasonTransformer {
          case e: vprrea.InsufficientPermission if e causedBy guardPredicateAccess.loc =>
            InsufficientGuardPermissionError(guardExp)
        }

        guardPredicateAccess
    }
  }

  def translateUseOf(region: PRegion,
                     guardDecl: PGuardDecl,
                     actualRegionId: vpr.Exp,
                     source: Option[PAstNode])
                    : vpr.PredicateAccessPredicate = {

    val vprGuardPredicate = guardPredicate(guardDecl, region)

    val guardPredicateAccess =
      vpr.PredicateAccessPredicate(
        vpr.PredicateAccess(
          Vector(actualRegionId),
          vprGuardPredicate.name
        )().withSource(source),
        vpr.FullPerm()()
      )().withSource(source)

    guardPredicateAccess
  }

  def havocSingleRegionInstance(region: PRegion,
                                regionArguments: Vector[PExpression],
                                preLabel: vpr.Label,
                                oldStateSnapshots: Option[(vpr.LocalVar, vpr.LocalVar)])
                               : RegionHavocCode = {

    havocRegionInstances(region, Some(regionArguments map translate), preLabel, oldStateSnapshots)
  }

  def havocAllRegionsInstances(region: PRegion, preLabel: vpr.Label): RegionHavocCode = {
    havocRegionInstances(region, None, preLabel, None)
  }

  /* TODO: Refactor */
  def havocRegionInstances(region: PRegion,
                           specificInstance: Option[Vector[vpr.Exp]],
                           preLabel: vpr.Label,
                           oldStateSnapshots: Option[(vpr.LocalVar, vpr.LocalVar)])
                          : RegionHavocCode = {

    require(oldStateSnapshots.isEmpty || specificInstance.nonEmpty,
            s"It is currently not possible to havoc all instances of a particular region " +
            s"(argument 'specificInstance' is 'None') while using an old state snapshots " +
            s"(argument 'oldStateSnapshots' is '$oldStateSnapshots')")

    val (regionId, regionArguments) =
      specificInstance match {
        case Some(args) =>
          (args.head, args)

        case None =>
          val args = region.formalInArgs map (a => vpr.LocalVar(s"$$${a.id.name}")(typ = translate(a.typ)))
          val id = args.head

          (id, args)
      }

    def potentiallyQuantify(body: vpr.Exp, trigger: Option[vpr.Exp]): vpr.Exp = {
      if (specificInstance.nonEmpty)
        body
      else {
        vpr.Forall(
          regionArguments
            .map(_.asInstanceOf[vpr.LocalVar]) // TODO: Get rid of casts
            .map(v => vpr.LocalVarDecl(v.name, v.typ)()),
          trigger.map(e => vpr.Trigger(Vector(e))()).toSeq,
          body
        )()
      }
    }

    val comment =
      vpr.SimpleInfo(
        Vector(
          "",
          if (specificInstance.nonEmpty)
            s"Havocking region ${region.id.name}(${regionArguments.mkString(", ")})"
          else
            s"Havocking all held instances of region ${region.id.name}"))

    /* region_state(args) */
    val state =
      vpr.FuncApp(
        regionStateFunction(region),
        regionArguments)()

    val preHavocState =
      oldStateSnapshots match {
        case None => vpr.LabelledOld(state, preLabel.name)()
        case Some((variable, _)) => variable
      }

    /* region(args) */
    val regionPredicateInstance =
      vpr.PredicateAccess(
        args = regionArguments,
        predicateName = region.id.name
      )()

    /* perm(region(args)) */
    val currentPermissions = vpr.CurrentPerm(regionPredicateInstance)()

    val preHavocPermissions =
      oldStateSnapshots match {
        case None => vpr.LabelledOld(currentPermissions, preLabel.name)()
        case Some((_, variable)) => variable
      }

    /* acc(region(args), p) */
    def regionPredicateAccess(p: vpr.Exp) =
      vpr.PredicateAccessPredicate(
        loc = regionPredicateInstance,
        perm = p
      )()

    val regionPredicateHeld =
      if (specificInstance.nonEmpty)
        vpr.TrueLit()()
      else
        vpr.PermLtCmp(
          vpr.NoPerm()(),
          currentPermissions
        )()

    /* exhale region(args) */
    val vprExhaleRegion =
      vpr.Exhale(potentiallyQuantify(regionPredicateAccess(currentPermissions), None))()

    /* inhale region(args) */
    val vprInhaleRegion =
      vpr.Inhale(potentiallyQuantify(regionPredicateAccess(preHavocPermissions), None))()

    def potentialStateValuesPerGuard(guard: PGuardDecl): vpr.Exp = {
      val potentiallyHeld =
          vpr.FuncApp(
            guardPotentiallyHeldFunction(guard, region),
            Vector(
              regionId,
              vpr.LabelledOld(
                vpr.CurrentPerm(
                  vpr.PredicateAccess(
                    Vector(regionId),
                    guardPredicate(guard, region).name
                  )()
                )(),
                preLabel.name
              )())
          )()

        val closureSet =
          vpr.FuncApp(
            guardTransitiveClosureFunction(guard, region),
            Vector(
              regionId,
              preHavocState)
          )()

        vpr.CondExp(
          potentiallyHeld,
          closureSet,
          vpr.ExplicitSet(Vector(preHavocState))()
        )()
    }

    val constrainStateViaGuards = {
      val interferenceSet = {
        val init = potentialStateValuesPerGuard(region.guards.head)

        region.guards.tail.foldLeft(init)((set, guard) => {
          vpr.AnySetUnion(
            set,
            potentialStateValuesPerGuard(guard)
          )()
        })
      }

      val stateConstraint =
        vpr.Implies(
          regionPredicateHeld,
          vpr.AnySetContains(
            state,
            interferenceSet
          )()
        )()

      vpr.Inhale(
        potentiallyQuantify(
          body = stateConstraint,
          trigger = Some(regionStateTriggerFunctionApplication(state)))
      )()
    }

    val constrainStateViaAtomicityContext = {
      val diamondHeld =
        vpr.PermLtCmp(
          vpr.NoPerm()(),
          vpr.CurrentPerm(
            diamondAccess(regionId).loc
          )()
        )()

      val atomicityContextX =
        vpr.DomainFuncApp(
          atomicityContextFunction(region),
          regionArguments,
          Map.empty[vpr.TypeVar, vpr.Type]
        )()

      val stateConstraint =
        potentiallyQuantify(
          body =
            vpr.Implies(
              vpr.And(
                regionPredicateHeld,
                diamondHeld
              )(),
              vpr.AnySetContains(
                state,
                atomicityContextX
              )()
            )(),
          trigger = Some(regionStateTriggerFunctionApplication(state)))

      vpr.Inhale(stateConstraint)()
    }

    RegionHavocCode(
      comment,
      vprExhaleRegion,
      vprInhaleRegion,
      constrainStateViaGuards,
      constrainStateViaAtomicityContext)
  }
}

case class RegionHavocCode(leadingComment: vpr.SimpleInfo,
                           exhale: vpr.Exhale,
                           inhale: vpr.Inhale,
                           constrainStateViaGuards: vpr.Inhale,
                           constrainStateViaAtomicityContext: vpr.Inhale) {

  val asSeqn: vpr.Seqn =
    vpr.Seqn(
      Vector(
        exhale,
        inhale,
        constrainStateViaGuards,
        constrainStateViaAtomicityContext),
      Vector.empty
    )(info = leadingComment)
}
