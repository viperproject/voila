/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver.ast.Trigger
import viper.silver.ast.utility.Rewriter.Traverse

import scala.collection.breakOut
import viper.silver.{ast => vpr}
import viper.silver.verifier.{errors => vprerr, reasons => vprrea}
import viper.voila.backends.ViperAstUtils
import viper.voila.frontend._
import viper.voila.reporting.{FoldError, InsufficientRegionPermissionError, InterferenceError, PreconditionError, RegionStateError, UnfoldError}


trait StabilizationComponent { this: PProgramToViperTranslator =>

  def stabilizeSingleInstances(reason: String, regions: (PRegion, Vector[vpr.Exp])*): vpr.Stmt = {
    val stabilizationMessage =
      s"Stabilising regions ${regions.map(_._1.id.name).mkString(",")} ($reason)"

    outputDebugInfo(stabilizationMessage)

    val preHavocLabel = freshLabel("pre_havoc")

    val stabilizeInstances =
      regions.map(region =>
        prependComment(
          s"Stabilising single instance of region ${region._1.id.name}",
          stabilizeOneInstancesOfSingleRegion(region._1, region._2, preHavocLabel)))

    val result =
      vpr.Seqn(
        preHavocLabel +: stabilizeInstances,
        Vector.empty
      )()

    surroundWithSectionComments(stabilizationMessage, result)
  }

  def stabilizeAllInstances(reason: String): vpr.Stmt = {
    stabilizeAllInstances(reason, tree.root.regions : _*)
  }

  def stabilizeAllInstances(reason: String, regions: PRegion*): vpr.Stmt = {
    val stabilizationMessage =
      s"Stabilising regions ${regions.map(_.id.name).mkString(",")} ($reason)"

    outputDebugInfo(stabilizationMessage)

    val preHavocLabel = freshLabel("pre_havoc")

    val stabilizeInstances =
      regions.map(region =>
        prependComment(
          s"Stabilising all instances of region ${region.id.name}",
          stabilizeAllInstancesOfSingleRegion(region, preHavocLabel)))

    val result =
      vpr.Seqn(
        preHavocLabel +: stabilizeInstances,
        Vector.empty
      )()

    surroundWithSectionComments(stabilizationMessage, result)
  }

  private def generateCodeForHavocingAllRegionInstances(
                                                         region: PRegion,
                                                         prePermissions: vpr.Exp => vpr.Exp)
  : vpr.Seqn = {
    allRegionInstanceApplication(region)(generateCodeForHavocingRegionInstances(region, prePermissions))
  }


  private def stabilizeOneInstancesOfSingleRegion(region: PRegion,
                                                  regionArguments: Vector[vpr.Exp],
                                                  preHavocLabel: vpr.Label)
  : vpr.Seqn = {

    val singleTransitionWrap = (exp: vpr.Exp) =>
      vpr.Seqn(
        Vector(vpr.Inhale(exp)()),
        Vector.empty
      )()

    generateCodeForStabilizingRegionInstances(
      region,
      dfltActionFilter(region),
      dfltPreRegionState(region, preHavocLabel),
      dfltPostRegionState(region),
      dfltPrePermissions(preHavocLabel)
    )(
      regionArguments,
      dfltSingleHavocWrap,
      singleTransitionWrap
    )
  }

  private def stabilizeAllInstancesOfSingleRegion(region: PRegion,
                                                  preHavocLabel: vpr.Label)
  : vpr.Seqn = {

    /* Arguments as for region R */
    val vprRegionArgumentDecls: Vector[vpr.LocalVarDecl] = region.formalInArgs.map(translate)

    /* Arguments as for region R */
    val vprRegionArguments: Vector[vpr.LocalVar] = vprRegionArgumentDecls map (_.localVar)

    /* ∀ as · acc(R(as), π) */
    val allTransitionWrap = (exp: vpr.Exp) =>
      vpr.Seqn(
        Vector(vpr.Inhale(
          vpr.Forall(
            variables = vprRegionArgumentDecls,
            triggers = Vector(vpr.Trigger(Vector(
              regionStateTriggerFunctionApplication(vpr.FuncApp(regionStateFunction(region), vprRegionArguments)())
            ))()),
            exp = exp
          )()
        )()),
        Vector.empty
      )()

    generateCodeForStabilizingRegionInstances(
      region,
      dfltActionFilter(region),
      dfltPreRegionState(region, preHavocLabel),
      dfltPostRegionState(region),
      dfltPrePermissions(preHavocLabel)
    )(
      vprRegionArguments,
      dfltAllHavocWrap(vprRegionArgumentDecls),
      allTransitionWrap
    )
  }

  private def dfltActionFilter(region: PRegion)(action: PAction): Boolean = true

  private def dfltPostRegionState(region: PRegion)(args: Vector[vpr.Exp]): vpr.Exp =
    vpr.FuncApp(regionStateFunction(region), args)()

  private def dfltPreRegionState(region: PRegion, preLabel: vpr.Label)(args: Vector[vpr.Exp]): vpr.Exp =
    vpr.LabelledOld(vpr.FuncApp(regionStateFunction(region), args)(), preLabel.name)()

  private def dfltPrePermissions(preLabel: vpr.Label)(exp: vpr.Exp): vpr.Exp =
    vpr.LabelledOld(exp, preLabel.name)()

  private def dfltSingleHavocWrap(exp: vpr.Exp): vpr.Exp = exp

  private def dfltAllHavocWrap(vprRegionArgumentDecls: Vector[vpr.LocalVarDecl])(exp: vpr.Exp): vpr.Exp =
    vpr.Forall(
      variables = vprRegionArgumentDecls,
      triggers = Vector.empty, /* TODO: Picking triggers not yet possible due to Viper limitations */
      exp = exp
    )()

  private def generateCodeForStabilizingRegionInstances(region: PRegion,
                                                        actionFilter: PAction => Boolean,
                                                        preRegionState: Vector[vpr.Exp] => vpr.Exp,
                                                        postRegionState: Vector[vpr.Exp] => vpr.Exp,
                                                        prePermissions: vpr.Exp => vpr.Exp)
                                                       (vprRegionArguments: Vector[vpr.Exp],
                                                        havocWrap: vpr.Exp => vpr.Exp,
                                                        transitionWrap: vpr.Exp => vpr.Seqn)
  : vpr.Seqn = {

    val havocCode = generateCodeForHavocingRegionInstances(
      region,
      prePermissions
    )(vprRegionArguments, havocWrap)

    val transitionCode = generateCodeForConstrainingRegionTransitions(
      region,
      actionFilter,
      preRegionState,
      postRegionState,
      prePermissions
    )(vprRegionArguments, transitionWrap)

    val skolemizedTransitionCode = skolemizeCodeForRegionTransition(
      region,
      vprRegionArguments,
      transitionCode
    )

    val result = vpr.Seqn(
      Vector(
        havocCode,
        skolemizedTransitionCode
      ),
      Vector.empty
    )()

    ViperAstUtils.sanitizeBoundVariableNames(result) // TODO: not sure yet where it is best to sanitize
  }

  private def skolemizeCodeForRegionTransition(region: PRegion,
                                               skolemArgs: Vector[vpr.Exp],
                                               codeForRegionTransition: vpr.Seqn)
  : vpr.Seqn = {

    val vprPreliminaryResult = codeForRegionTransition

    /* Skolemize action existentials */

    def substitute(v: vpr.LocalVar, qvars: Seq[vpr.LocalVar]): vpr.Exp = {
      vpr.FuncApp(
        collectedActionSkolemizationFunctions(region.id.name, v.name),
        skolemArgs
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

    val vprResult =
      vprSkolemizedResult.copy(
        ss =
          Vector(vprExhaleActionSkolemizationFunctionFootprint,
            vprInhaleActionSkolemizationFunctionFootprint) ++
            vprSkolemizedResult.ss
      )(vprSkolemizedResult.pos, vprSkolemizedResult.info, vprSkolemizedResult.errT)

    vprResult
  }

  private def generateCodeForHavocingRegionInstances( region: PRegion,
                                                      prePermissions: vpr.Exp => vpr.Exp)
                                                    ( vprRegionArguments: Vector[vpr.Exp],
                                                      havocWrap: vpr.Exp => vpr.Exp)
  : vpr.Seqn = {
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

    val vprWrappedRegionAssertion = havocWrap(vprRegionAssertion)

    /* exhale ∀ as · acc(R(as), π) */
    val vprExhaleAllRegionInstances = vpr.Exhale(vprWrappedRegionAssertion)()

    /* inhale ∀ as · acc(R(as), π) */
    val vprInhaleAllRegionInstances = vpr.Inhale(vprWrappedRegionAssertion)()

    vpr.Seqn(
      Vector(
        vprExhaleAllRegionInstances,
        vprInhaleAllRegionInstances
      ),
      Vector.empty
    )()
  }

  private def generateCodeForConstrainingRegionTransitions(region: PRegion,
                                                           actionFilter: PAction => Boolean,
                                                           preRegionState: Vector[vpr.Exp] => vpr.Exp,
                                                           postRegionState: Vector[vpr.Exp] => vpr.Exp,
                                                           prePermissions: vpr.Exp => vpr.Exp)
                                                          (vprRegionArguments: Vector[vpr.Exp],
                                                           transitionWrap: vpr.Exp => vpr.Seqn)
  : vpr.Seqn = {

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

    /* R_state(as) */
    val vprPreRegionState = preRegionState(vprRegionArguments)

    /* R_state'(as) */
    val vprPostRegionState = postRegionState(vprRegionArguments)

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

    transitionWrap(vprConstrainStateIfRegionAccessible)
  }

  private def singleRegionInstanceApplication(region: PRegion,
                                              vprRegionInArgs: Vector[vpr.Exp])
                                             (func: (Vector[vpr.Exp], vpr.Exp => vpr.Exp) => vpr.Seqn)
  : vpr.Seqn = func(vprRegionInArgs, identity)

  private def allRegionInstanceApplication(region: PRegion, triggers: Seq[Trigger] = Vector.empty)
                                          (func: (Vector[vpr.Exp], vpr.Exp => vpr.Exp) => vpr.Seqn)
  : vpr.Seqn = {

    /* Arguments as for region R */
    val vprRegionArgumentDecls: Vector[vpr.LocalVarDecl] = region.formalInArgs.map(translate)

    /* Arguments as for region R */
    val vprRegionArguments: Vector[vpr.LocalVar] = vprRegionArgumentDecls map (_.localVar)


    /* ∀ as · acc(R(as), π) */
    val vprQuantifiedRegionAssertion = (vprRegionAssertion: vpr.Exp) =>
      vpr.Forall(
        variables = vprRegionArgumentDecls,
        triggers = triggers, /* TODO move todo: TODO: Picking triggers not yet possible due to Viper limitations */
        exp = vprRegionAssertion
      )()

    func(vprRegionArguments, vprQuantifiedRegionAssertion)
  }

}
