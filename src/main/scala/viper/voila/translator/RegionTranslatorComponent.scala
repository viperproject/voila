/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.mutable
import viper.voila.frontend._
import viper.silver.{ast => vpr}

trait RegionTranslatorComponent { this: PProgramToViperTranslator =>
  private val regionStateFunctionCache =
    mutable.Map.empty[PRegion, vpr.Function]

  private val guardTransitiveClosureFunctionCache =
    mutable.Map.empty[(PGuardDecl, PRegion), vpr.Function]

  private val guardPotentiallyHeldFunctionCache =
    mutable.Map.empty[(PGuardDecl, PRegion), vpr.Function]

  private val guardPredicateCache =
    mutable.Map.empty[(PGuardDecl, PRegion), vpr.Predicate]

  def regionPredicateAccess(region: PRegion, arguments: Vector[vpr.Exp])
                           : vpr.PredicateAccessPredicate =
  {
    vpr.PredicateAccessPredicate(
      loc = vpr.PredicateAccess(
                args = arguments,
                predicateName = region.id.name
            )(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos),
      perm = vpr.FullPerm()()
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
        val fromTyp = translateNonVoid(semanticAnalyser.typ(region.actions.head.from))
        val toTyp = translateNonVoid(semanticAnalyser.typ(region.actions.head.to))

        val formalArgs =
          Vector(
            vpr.LocalVarDecl("$r", translateNonVoid(PRegionIdType()))(),
            vpr.LocalVarDecl("$from", fromTyp)())

        val body = {
          val from = formalArgs(1).localVar
          val fromSet = vpr.ExplicitSet(Vector(from))()

          region.actions
            .filter(_.guard.name == guard.id.name)
            .foldLeft(fromSet: vpr.Exp)((acc, action) => {
              vpr.CondExp(
                cond = vpr.EqCmp(from, translate(action.from))(),
                thn = translate(action.to),
                els = acc
              )()
            })
        }

        vpr.Function(
          name = guardTransitiveClosureFunctionName(guard, region),
          formalArgs = formalArgs,
          typ = toTyp,
          pres = Vector.empty,
          posts = Vector.empty,
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

  def translateUseOf(regionPredicate: PPredicateExp): vpr.Exp = {
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

    val vprRegionAccess =
      vpr.PredicateAccess(
        args = vprRegionArguments,
        predicateName = region.id.name
      )(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)

    vpr.And(vprRegionAccess, vprStateConstraint)()
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

  def translate(guardExp: PGuardExp): vpr.Exp = {
    semanticAnalyser.entity(guardExp.guard) match {
      case GuardEntity(guardDecl, region) =>
        val vprGuardPredicate = guardPredicate(guardDecl, region)

        val guardPredicateAccess =
          vpr.PredicateAccessPredicate(
            loc = vpr.PredicateAccess(
                    args = Vector(translate(PIdnExp(guardExp.regionId))),
                    predicate = vprGuardPredicate
                  )(pos = vpr.NoPosition, info = vpr.NoInfo),
            perm = vpr.FullPerm()()
          )()

        guardPredicateAccess
    }
  }

  def havocRegion(region: PRegion, regionArguments: Vector[PExpression]): vpr.Seqn = {
    val regionId = regionArguments.head.asInstanceOf[PIdnExp].id
    val vprArgs @ (vprRegionIdArg +: _) = regionArguments map translate

    val vprTmpVar = temporaryVariable(semanticAnalyser.typ(region.state)).localVar
    val atomicityContextX = atomicityContextVariable(regionId).localVar

    val comment =
      vpr.SimpleInfo(
        Vector(
          "",
          s"${region.id.name}_havoc(${(vprArgs :+ atomicityContextX :+ vprTmpVar).mkString(", ")})"))

    val state =
      vpr.FuncApp(
        regionStateFunction(region),
        vprArgs)()

    /* tmp := region_state(arguments) */
    val saveRegionState =
      vpr.LocalVarAssign(
        vprTmpVar,
        state
      )()

    /* Set(tmp) */
    val currentSet =
      vpr.ExplicitSet(Vector(vprTmpVar))()

    /* region(arguments) */
    val predicateAccess =
      regionPredicateAccess(region, vprArgs)

    /* exhale region(arguments);  inhale region(arguments) */
    val havocRegion =
      vpr.Seqn(
        Vector(
          vpr.Exhale(predicateAccess)(),
          vpr.Inhale(predicateAccess)())
      )()

    def potentialStateValuesPerGuard(guard: PGuardDecl): vpr.Exp = {
      val potentiallyHeld =
          vpr.FuncApp(
            guardPotentiallyHeldFunction(guard, region),
            Vector(
              vprRegionIdArg,
              vpr.CurrentPerm(
                vpr.PredicateAccess(
                  Vector(vprRegionIdArg),
                  guardPredicate(guard, region)
                )()
              )())
          )()

        val closureSet =
          vpr.FuncApp(
            guardTransitiveClosureFunction(guard, region),
            Vector(
              vprRegionIdArg,
              vprTmpVar)
          )()

        vpr.CondExp(
          potentiallyHeld,
          closureSet,
          currentSet
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

      vpr.Inhale(
        vpr.AnySetContains(
          state,
          interferenceSet
        )()
      )()
    }

    val constrainStateViaAtomicityContext = {
      val diamondHeld =
        vpr.PermLtCmp(
          vpr.NoPerm()(),
          vpr.CurrentPerm(
            diamondAccess(vprRegionIdArg).loc
          )()
        )()

      vpr.Inhale(
        vpr.Implies(
          diamondHeld,
          vpr.AnySetContains(
            state,
            atomicityContextX
          )()
        )()
      )()
    }

    vpr.Seqn(
      Vector(
        saveRegionState,
        havocRegion,
        constrainStateViaGuards,
        constrainStateViaAtomicityContext)
    )(info = comment)
  }
}
