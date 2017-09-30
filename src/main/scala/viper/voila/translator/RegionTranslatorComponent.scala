/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.mutable
import viper.voila.frontend._
import viper.voila.reporting.{InsufficientRegionPermissionError, RegionStateError}
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

  def regionStateFunctionName(region: PRegion): String =
    s"${region.id.name}_state"

  def regionStateFunction(region: PRegion): vpr.Function = {
    regionStateFunctionCache.getOrElseUpdate(
      region,
      {
        val formalRegionArg = translate(region.regionId)
        val formalRegularArgs = region.formalArgs map translate
        val regionStateType = translateNonVoid(semanticAnalyser.typ(region.state))

        /* acc(region(id, args)) */
        val predicateAccess =
          regionPredicateAccess(
            region,
            formalRegionArg.localVar +: formalRegularArgs.map(_.localVar))

        val stateFunctionBody =
          vpr.Unfolding(
            acc = predicateAccess,
            body = translate(region.state)
          )()

        vpr.Function(
          name = regionStateFunctionName(region),
          formalArgs = formalRegionArg +: formalRegularArgs,
          typ = regionStateType,
          pres = Vector(predicateAccess),
          posts = Vector.empty,
          decs = None,
          body = Some(stateFunctionBody)
        )()
      })
  }

  def guardPotentiallyHeldFunctionName(guard: PGuardDecl, region: PRegion): String =
    s"${region.id.name}_${guard.id.name}_potentiallyHeldByEnvironment"

  def guardPotentiallyHeldFunction(guard: PGuardDecl, region: PRegion): vpr.Function = {
    guardPotentiallyHeldFunctionCache.getOrElseUpdate(
      (guard, region),
      {
        val formalArgs =
          Vector(
            vpr.LocalVarDecl("$r", translateNonVoid(PRegionIdType()))(),
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
        val regionType = translateNonVoid(semanticAnalyser.typ(region.state))

        val formalArgs =
          Vector(
            vpr.LocalVarDecl("$r", translateNonVoid(PRegionIdType()))(),
            vpr.LocalVarDecl("$from", regionType)())

        val body = {
          val from = formalArgs(1).localVar
          val fromSet = vpr.ExplicitSet(Vector(from))()
          val actions = region.actions.filter(_.guard.name == guard.id.name)

          require(
            actions.count(_.from.isInstanceOf[PLogicalVariableBinder]) <= 1,
               "Cannot yet handle cases in which more than one action per guard binds a "
            + s"variable: $actions")

          /* Note: translation scheme needs to be generalised in order to support a generalised
           * source syntax, e.g. to the shape `?x if p(x) ~> Set(y | q(x, y))`.
           */
          actions
            .foldLeft(fromSet: vpr.Exp)((acc, action) => {
              action.from match {
                case PLogicalVariableBinder(iddef) =>
                  /* Source: ?x ~> e(x)
                   * Encode: e(from)
                   */
                  translate(action.to).transform {
                    case vpr.LocalVar(iddef.name) => from /* TODO: Fragile, relies on 'x' being translated to 'x' */
                  }

                case _ =>
                  /* Source: e ~> e'
                   * Encode: from == e ? e' : Set(from)
                   */
                  vpr.CondExp(
                    cond = vpr.EqCmp(from, translate(action.from))(),
                    thn = translate(action.to),
                    els = acc
                  )()
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
        formalArgs = Vector(vpr.LocalVarDecl("$r", translateNonVoid(PRegionIdType()))()),
        body = None
      )()
    )
  }

  def translate(region: PRegion): Vector[vpr.Member] = {
    val regionPredicateName = region.id.name

    val formalRegionArg = translate(region.regionId)
    val formalRegularArgs = region.formalArgs map translate

    /* predicate region(id, args) { interpretation } */
    val regionPredicate =
      vpr.Predicate(
        name = regionPredicateName,
        formalArgs = formalRegionArg +: formalRegularArgs,
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

    val stateFunction = regionStateFunction(region)

    (   guardPredicates
     ++ potentiallyHeldFunctions
     ++ transitiveClosureFunctions
     ++  Vector(
            regionPredicate,
            stateFunction))
  }

  def translateUseOf(regionPredicate: PPredicateExp): (vpr.PredicateAccessPredicate, vpr.Exp) = {
    val (region, vprRegionArguments, vprRegionStateArgument) =
      getAndTranslateRegionPredicateDetails(regionPredicate)

    val vprStateConstraint =
      vprRegionStateArgument match {
        case None | Some(Left(_: PLogicalVariableBinder)) => vpr.TrueLit()()
        case Some(Right(vprStateArgument)) =>
          val vprStateFunction = regionStateFunction(region)

          vprStateArgument match {
            case app: vpr.FuncApp if app.funcname == vprStateFunction.name =>
              /* Avoid generation of redundant constraints of the shape state(a, x) == state(a, x).
               * Should not be necessary in the long run.
               */
              vpr.TrueLit()()
            case _ =>
              vpr.EqCmp(
                vpr.FuncApp(
                  func = vprStateFunction,
                  args = vprRegionArguments
                )(),
                vprStateArgument
              )()
          }
      }

    val vprRegionPredicate =
      vpr.PredicateAccess(
        args = vprRegionArguments,
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
                               : (PRegion, Vector[PExpression], Option[Either[PLogicalVariableBinder, PExpression]]) = {

    val region =
      semanticAnalyser.entity(predicateExp.predicate)
                      .asInstanceOf[RegionEntity]
                      .declaration

    val (regionArguments, regionStateArgument) =
      predicateExp.arguments.splitAt(region.formalArgs.length + 1) match {
        case (args, Seq()) => (args, None)
        case (args, Seq(binder: PLogicalVariableBinder)) => (args, Some(Left(binder)))
        case (args, Seq(arg)) => (args, Some(Right(arg)))
        case _ => sys.error(s"Unexpectedly many arguments: $predicateExp")
      }

    (region, regionArguments, regionStateArgument)
  }

  def getAndTranslateRegionPredicateDetails(predicateExp: PPredicateExp)
                                           : (PRegion, Vector[vpr.Exp], Option[Either[PLogicalVariableBinder, vpr.Exp]]) = {

    val (region, regionArguments, regionStateArgument) = getRegionPredicateDetails(predicateExp)
    val vprRegionStateArgument = regionStateArgument.map(_.right.map(translate))

    (region, regionArguments map translate, vprRegionStateArgument)
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
        val vprGuardPredicate = guardPredicate(guardDecl, region)

        val guardPredicateAccess =
          vpr.PredicateAccessPredicate(
            vpr.PredicateAccess(
              Vector(translateUseOf(guardExp.regionId)),
              vprGuardPredicate.name
            )(),
            vpr.FullPerm()()
          )()

        guardPredicateAccess
    }
  }

  // TODO: Unify fresh label code

  private var lastPreHavocLabel: vpr.Label = _
  private var preHavocCounter = 0

  def freshPreHavocLabel(): vpr.Label = {
    preHavocCounter += 1

    val label =
      vpr.Label(
        s"pre_havoc_$preHavocCounter",
        Vector.empty
      )()

    lastPreHavocLabel = label

    label
  }

  def havocSingleRegionInstance(region: PRegion, regionArguments: Vector[PExpression]): vpr.Seqn = {
    val regionId = regionArguments.head.asInstanceOf[PIdnExp].id
    val atomicityContextX = atomicityContextVariable(regionId).localVar

    havocRegionInstances(region, Some((regionArguments map translate, atomicityContextX)))
  }

  def havocAllRegionsInstances(region: PRegion): vpr.Seqn =
    havocRegionInstances(region, None)

  private def havocRegionInstances(region: PRegion,
                                   specificInstance: Option[(Vector[vpr.Exp], vpr.Exp)])
                                  : vpr.Seqn = {

    val (regionId, regionArguments) =
      specificInstance match {
        case Some((args, _)) =>
          (args.head, args)
        case None =>
          val idArg = vpr.LocalVar(s"$$${region.regionId.id.name}")(typ = translateNonVoid(region.regionId.typ))
          val furtherArgs = region.formalArgs map (a => vpr.LocalVar(s"$$${a.id.name}")(typ = translateNonVoid(a.typ)))
          (idArg, idArg +: furtherArgs)
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

    val preHavocLabel = freshPreHavocLabel()

    /* region_state(args) */
    val state =
      vpr.FuncApp(
        regionStateFunction(region),
        regionArguments)()

    /* old[pre_havoc](region_state(args)) */
    val preHavocState =
      vpr.LabelledOld(state, preHavocLabel.name)()

    /* region(args) */
    val regionPredicateInstance =
      vpr.PredicateAccess(
        args = regionArguments,
        predicateName = region.id.name
      )()

    /* perm(region(args)) */
    val currentPermissions = vpr.CurrentPerm(regionPredicateInstance)()

    /* old[pre_havoc](perm(region(args))) */
    val preHavocPermissions =
      vpr.LabelledOld(currentPermissions, preHavocLabel.name)()

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

    /* exhale region(args);  inhale region(args) */
    val havocRegion =
      vpr.Seqn(
        Vector(
          vpr.Exhale(potentiallyQuantify(regionPredicateAccess(currentPermissions), None))(),
          vpr.Inhale(potentiallyQuantify(regionPredicateAccess(preHavocPermissions), None))()),
        Vector.empty
      )()

    def potentialStateValuesPerGuard(guard: PGuardDecl): vpr.Exp = {
      val potentiallyHeld =
          vpr.FuncApp(
            guardPotentiallyHeldFunction(guard, region),
            Vector(
              regionId,
              vpr.CurrentPerm(
                vpr.PredicateAccess(
                  Vector(regionId),
                  guardPredicate(guard, region).name
                )()
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

      vpr.Inhale(potentiallyQuantify(stateConstraint, Some(state)))()
    }

    val constrainStateViaAtomicityContext = {
      val diamondHeld =
        vpr.PermLtCmp(
          vpr.NoPerm()(),
          vpr.CurrentPerm(
            diamondAccess(regionId).loc
          )()
        )()

      val stateConstraint =
        specificInstance match {
          case Some((_, atomicityContextX)) =>
            vpr.Implies(
              vpr.And(
                regionPredicateHeld,
                diamondHeld
              )(),
              vpr.AnySetContains(
                state,
                atomicityContextX
              )()
            )()
          case None =>
            vpr.TrueLit()()
        }

      vpr.Inhale(stateConstraint)()
    }

    vpr.Seqn(
      Vector(
        preHavocLabel,
        havocRegion,
        constrainStateViaGuards,
        constrainStateViaAtomicityContext),
      Vector.empty
    )(info = comment)
  }
}
