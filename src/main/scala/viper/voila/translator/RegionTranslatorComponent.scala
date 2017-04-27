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
            )(pos = vpr.NoPosition, info = vpr.NoInfo),
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
          _pres = Vector(predicateAccess),
          _posts = Vector.empty,
          _body = Some(stateFunctionBody)
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
            vpr.LocalVarDecl("$p", vpr.Perm)()
          )

        val body =
          if (guard.duplicable) vpr.TrueLit()()
          else vpr.EqCmp(formalArgs(1).localVar, vpr.NoPerm()())()

        vpr.Function(
          name = guardPotentiallyHeldFunctionName(guard, region),
          formalArgs = formalArgs,
          typ = vpr.Bool,
          _pres = Vector.empty,
          _posts = Vector.empty,
          _body = Some(body)
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
            vpr.LocalVarDecl("$from", fromTyp)()
          )

        val body = {
          val from = formalArgs(1).localVar
          val fromSet = vpr.ExplicitSet(Vector(from))()

          region.actions.foldLeft(fromSet: vpr.Exp)((acc, action) => {
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
          _pres = Vector.empty,
          _posts = Vector.empty,
          _body = Some(body)
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
        _body = None
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
        _body = Some(translate(region.interpretation))
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

  def translateUseOf(region: PRegion, args: Vector[PExpression]): vpr.Exp = {
    val vprRegionId = translate(args.head)
    val (regularArgs, Seq(stateValue)) = args.tail.splitAt(args.length - 2)
    val vprRegularArgs = regularArgs map translate
    val vprRegionArguments = vprRegionId +: vprRegularArgs

    val vprStateConstraint =
      stateValue match {
        case PIrrelevantValue() =>
          vpr.TrueLit()()
        case _ =>
          val vprStateFunction = regionStateFunction(region)

          vpr.EqCmp(
            vpr.FuncApp(
              func = vprStateFunction,
              args = vprRegionArguments
            )(),
            translate(stateValue)
          )()
      }

    val vprRegionAccess =
      vpr.PredicateAccess(
        args = vprRegionArguments,
        predicateName = region.id.name
      )(vpr.NoPosition, vpr.NoInfo)

    vpr.And(vprRegionAccess, vprStateConstraint)()
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

  def havocRegion(region: PRegion,
                  arguments: Vector[PExpression],
                  atomicityContextX: PExpression,
                  tmpVar: vpr.LocalVar)
                 : vpr.Seqn =
  {
    val vprArgs @ (vprRegionIdArg +: _) = arguments map translate
    val vprCxtX = translate(atomicityContextX)

    val comment =
      vpr.SimpleInfo(
        Vector(
          "",
          s"${region.id.name}_havoc(${(vprArgs :+ vprCxtX :+ tmpVar).mkString(", ")})"))

    val state =
      vpr.FuncApp(
        regionStateFunction(region),
        vprArgs)()

    /* tmp := region_state(arguments) */
    val saveRegionState =
      vpr.LocalVarAssign(
        tmpVar,
        state
      )()

    /* Set(tmp) */
    val currentSet =
      vpr.ExplicitSet(Vector(tmpVar))()

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
              tmpVar)
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
            vprCxtX
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
