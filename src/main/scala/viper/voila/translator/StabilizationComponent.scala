/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver.ast.{Exp, Stmt, Trigger}
import viper.silver.ast.utility.Rewriter.Traverse

import scala.collection.breakOut
import viper.silver.{ast => vpr}
import viper.silver.verifier.{errors => vprerr, reasons => vprrea}
import viper.voila.backends.ViperAstUtils
import viper.voila.frontend._
import viper.voila.reporting.{FoldError, InsufficientRegionPermissionError, InterferenceError, PreconditionError, RegionStateError, UnfoldError}
import viper.voila.translator.TranslatorUtils.BetterQuantifierWrapper.WrapperExt
import viper.voila.translator.TranslatorUtils.{BetterQuantifierWrapper, Constraint}


trait StabilizationComponent { this: PProgramToViperTranslator =>

  object sequenceStabilizeSubject extends TranslatorUtils.Subject[Int] {
    private var version = 0

    def nextVersion: Unit = {
      version += 1
      notifyObservers(version)
    }
  }

  def stabilizeSingleInstances(reason: String, regions: (PRegion, Vector[vpr.Exp])*): vpr.Stmt = {
    val stabilizationMessage =
      s"Stabilising regions ${regions.map(_._1.id.name).mkString(",")} ($reason)"

    outputDebugInfo(stabilizationMessage)

    val preHavocLabel = freshLabel("pre_havoc")

    val stabilizeInstances =
      regions.map(region =>
        prependComment(
          s"Stabilising single instance of region ${region._1.id.name}",
          stabilizeOneInstancesOfSingleRegionWithInference(region._1, region._2, preHavocLabel)))

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
          stabilizeAllInstancesOfSingleRegionWithInference(region, preHavocLabel)))

    val result =
      vpr.Seqn(
        preHavocLabel +: stabilizeInstances,
        Vector.empty
      )()

    surroundWithSectionComments(stabilizationMessage, result)
  }

  private def stabilizeOneInstancesOfSingleRegion(region: PRegion,
                                                  regionArguments: Vector[vpr.Exp],
                                                  preHavocLabel: vpr.Label)
  : vpr.Seqn =
    generateCodeForStabilizingRegionInstances(
      region,
      dfltActionFilter(region),
      dfltPreRegionState(region, preHavocLabel),
      dfltPostRegionState(region),
      dfltPrePermissions(preHavocLabel)
    )(
      dfltSingleHavocWrapper(regionArguments),
      dfltSingleSelectWrapper(regionArguments)
    )

  private def stabilizeOneInstancesOfSingleRegionWithInference(region: PRegion,
                                                  regionArguments: Vector[vpr.Exp],
                                                  preHavocLabel: vpr.Label)
  : vpr.Seqn =
    generateCodeForStabilizingRegionInstances(
      region,
      dfltActionFilter(region),
      dfltPreRegionState(region, preHavocLabel),
      dfltPostRegionState(region),
      dfltPrePermissions(preHavocLabel)
    )(
      dfltSingleHavocWrapper(regionArguments),
      dfltSingleSelectWrapper(regionArguments).combine(interfereceWrapperExtension(region, dfltPostRegionState(region)))
    )

  private def stabilizeAllInstancesOfSingleRegion(region: PRegion,
                                                  preHavocLabel: vpr.Label)
  : vpr.Seqn =
    generateCodeForStabilizingRegionInstances(
      region,
      dfltActionFilter(region),
      dfltPreRegionState(region, preHavocLabel),
      dfltPostRegionState(region),
      dfltPrePermissions(preHavocLabel)
    )(
      dfltAllHavocWrapper(region),
      dfltAllSelectWrapper(region)
    )

  private def stabilizeAllInstancesOfSingleRegionWithInference(region: PRegion,
                                                  preHavocLabel: vpr.Label)
  : vpr.Seqn =
    generateCodeForStabilizingRegionInstances(
      region,
      dfltActionFilter(region),
      dfltPreRegionState(region, preHavocLabel),
      dfltPostRegionState(region),
      dfltPrePermissions(preHavocLabel)
    )(
      dfltAllHavocWrapper(region),
      dfltAllSelectWrapper(region).combine(interfereceWrapperExtension(region, dfltPostRegionState(region)))
    )


  private def dfltActionFilter(region: PRegion)(action: PAction): Boolean = true

  private def dfltPostRegionState(region: PRegion)(args: Vector[vpr.Exp]): vpr.Exp =
    vpr.FuncApp(regionStateFunction(region), args)()

  private def dfltPreRegionState(region: PRegion, preLabel: vpr.Label)(args: Vector[vpr.Exp]): vpr.Exp =
    vpr.LabelledOld(vpr.FuncApp(regionStateFunction(region), args)(), preLabel.name)()

  private def dfltPrePermissions(preLabel: vpr.Label)(exp: vpr.Exp): vpr.Exp =
    vpr.LabelledOld(exp, preLabel.name)()

  private def dfltSingleHavocWrapper(vprRegionArguments: Vector[vpr.Exp]): QuantifierWrapper.ExpWrapper =
    QuantifierWrapper.UnitWrapper[Vector[vpr.Exp],vpr.Exp](vprRegionArguments)(identity)

  private def dfltSingleSelectWrapper(vprRegionArguments: Vector[vpr.Exp]): QuantifierWrapper.StmtWrapper =
    QuantifierWrapper.UnitWrapper[Vector[vpr.Exp],vpr.Stmt](vprRegionArguments)(vpr.Inhale(_)())

  private def dfltAllHavocWrapper(region: PRegion): QuantifierWrapper.ExpWrapper = {

    /* Arguments as for region R */
    val vprRegionArgumentDecls: Vector[vpr.LocalVarDecl] = region.formalInArgs.map(translate)

    /* Arguments as for region R */
    val vprRegionArguments: Vector[vpr.LocalVar] = vprRegionArgumentDecls map (_.localVar)

    val triggers = Vector.empty /* TODO: Picking triggers not yet possible due to Viper limitations */

    QuantifierWrapper.AllWrapper[Vector[vpr.Exp],vpr.Exp](
      vprRegionArgumentDecls,
      vprRegionArguments,
      triggers
    )(
      identity,
      identity
    )
  }

  private def dfltAllSelectWrapper(region: PRegion): QuantifierWrapper.StmtWrapper = {

    /* Arguments as for region R */
    val vprRegionArgumentDecls: Vector[vpr.LocalVarDecl] = region.formalInArgs.map(translate)

    /* Arguments as for region R */
    val vprRegionArguments: Vector[vpr.LocalVar] = vprRegionArgumentDecls map (_.localVar)

    val triggers = Vector(vpr.Trigger(Vector(
      regionStateTriggerFunctionApplication(vpr.FuncApp(regionStateFunction(region), vprRegionArguments)())
    ))())

    QuantifierWrapper.AllWrapper[Vector[vpr.Exp],vpr.Stmt](
      vprRegionArgumentDecls,
      vprRegionArguments,
      triggers
    )(
      vpr.Inhale(_)(),
      identity
    )
  }



  private def generateCodeForStabilizingRegionInstances(region: PRegion,
                                                        actionFilter: PAction => Boolean,
                                                        preRegionState: Vector[vpr.Exp] => vpr.Exp,
                                                        postRegionState: Vector[vpr.Exp] => vpr.Exp,
                                                        prePermissions: vpr.Exp => vpr.Exp)
                                                       (havocWrap: QuantifierWrapper.ExpWrapper,
                                                        transitionWrap: QuantifierWrapper.StmtWrapper)
  : vpr.Seqn = {

    val havocCode = generateCodeForHavocingRegionInstances(
      region,
      prePermissions
    )(havocWrap)

    val transitionCode = generateCodeForConstrainingRegionTransitions(
      region,
      actionFilter,
      preRegionState,
      postRegionState,
      prePermissions
    )(transitionWrap)

    val skolemizedTransitionCode = skolemizeCodeForRegionTransition(
      region,
      transitionWrap.param,
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
                                               codeForRegionTransition: vpr.Stmt)
  : vpr.Stmt = {

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

    vpr.Seqn(
      Vector(vprExhaleActionSkolemizationFunctionFootprint,
        vprInhaleActionSkolemizationFunctionFootprint,
        vprSkolemizedResult
      ),
      Vector.empty
    )(vprSkolemizedResult.pos, vprSkolemizedResult.info, vprSkolemizedResult.errT)
  }

  private def generateCodeForHavocingRegionInstances( region: PRegion,
                                                      prePermissions: vpr.Exp => vpr.Exp)
                                                    ( wrapper: QuantifierWrapper.ExpWrapper)
  : vpr.Seqn = {

    val vprRegionArguments = wrapper.param

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

    val vprWrappedRegionAssertion = wrapper.wrap(vprRegionAssertion)

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
                                                          (wrapper: QuantifierWrapper.StmtWrapper)
  : vpr.Stmt = {

    val vprRegionArguments = wrapper.param

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

    wrapper.wrap(vprConstrainStateIfRegionAccessible)
  }



  case class RegionStateFrontResourceWrapper(prePermissions: vpr.Exp => vpr.Exp) extends TranslatorUtils.FrontResource[PRegion] {
    override def application(id: PRegion, args: Vector[Exp]): Exp =
      vpr.FuncApp(
        regionStateFunction(id),
        args
      )()

    override def applyTrigger(id: PRegion, args: Vector[Exp]): Vector[Trigger] =
      Vector(
        vpr.Trigger(
          Vector(
            vpr.DomainFuncApp(
              func = regionStateTriggerFunction(id.id.name),
              args = args,
              typVarMap = Map.empty
            )()
          ))())


    override def havoc(id: PRegion)(wrapper: BetterQuantifierWrapper.Wrapper): Stmt = {
      val vprRegionArguments = wrapper.args

      /* R(as) */
      val vprRegionPredicateInstance =
        vpr.PredicateAccess(
          args = vprRegionArguments,
          predicateName = id.id.name
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

      val vprWrappedRegionAssertion = wrapper.wrap(vprRegionAssertion)

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
  }


  def singleWrapper(args: Vector[vpr.Exp]): TranslatorUtils.BetterQuantifierWrapper.Wrapper =
    TranslatorUtils.BetterQuantifierWrapper.UnitWrapper(args)

  def regionAllWrapper(region: PRegion, prePermissions: vpr.Exp => vpr.Exp): TranslatorUtils.BetterQuantifierWrapper.Wrapper = {

    /* Arguments as for region R */
    val vprRegionArgumentDecls: Vector[vpr.LocalVarDecl] = region.formalInArgs.map(translate)

    /* Arguments as for region R */
    val vprRegionArguments: Vector[vpr.LocalVar] = vprRegionArgumentDecls map (_.localVar)

    /* R(as) */
    val vprRegionPredicateInstance =
      vpr.PredicateAccess(
        args = vprRegionArguments,
        predicateName = region.id.name
      )()

    /* π */
    val vprPreHavocRegionPermissions =
      prePermissions(vpr.CurrentPerm(vprRegionPredicateInstance)())

    /* none < π */
    val vprIsRegionAccessible =
      vpr.PermLtCmp(
        vpr.NoPerm()(),
        vprPreHavocRegionPermissions
      )()

    TranslatorUtils.BetterQuantifierWrapper.QuantWrapper(vprRegionArgumentDecls, vprRegionArguments, vprIsRegionAccessible)
  }






  def possibleNextStateConstraint(region: PRegion,
                                  actionFilter: PAction => Boolean,
                                  preRegionState: Vector[vpr.Exp] => vpr.Exp)
  : Constraint = {

    def constrain(args: Vector[Exp])(target: Exp): WrapperExt = {

      val vprRegionArguments = args

      /* First element a_0 of region arguments as */
      val vprRegionId = vprRegionArguments.head

      /* R_state(as) */
      val vprPreRegionState = preRegionState(vprRegionArguments)

      /* m ~ R_state'(as) */
      val vprPostRegionState = target

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

      TranslatorUtils.BetterQuantifierWrapper.UnitWrapperExt(vprConstrainRegionState)
    }

    Constraint(constrain, Some(args => s => skolemizeCodeForRegionTransition(region, args, s)))
  }

  object QuantifierWrapper {

    sealed trait WrapperExt {
      def combine(func: vpr.Exp => WrapperExt): WrapperExt
    }
    case class UnitWrapperExt(exp: Exp) extends WrapperExt {
      override def combine(func: Exp => WrapperExt): WrapperExt = func(exp)
    }
    case class QuantWrapperExt(decls: Vector[vpr.LocalVarDecl], exp: Exp) extends WrapperExt {
      override def combine(func: Exp => WrapperExt): WrapperExt = func(exp) match {
        case UnitWrapperExt(e) => QuantWrapperExt(decls, e)
        case QuantWrapperExt(ds, e) => QuantWrapperExt(decls ++: ds, e)
      }
    }



    sealed trait Wrapper[X,S,T] {
      def param: X
      def combine[Z](func: Wrapper[X,S,T] => Wrapper[Z,S,T]): Wrapper[Z,S,T]
      def wrap(in: S): T
    }

    type ExpWrapper = Wrapper[Vector[vpr.Exp], vpr.Exp, vpr.Exp]
    type StmtWrapper = Wrapper[Vector[vpr.Exp], vpr.Exp, vpr.Stmt]

    case class UnitWrapper[X,T](param: X)(_wrap: vpr.Exp => T) extends Wrapper[X,vpr.Exp,T] {
      def combine[Z](func: Wrapper[X,vpr.Exp,T] => Wrapper[Z,vpr.Exp,T]): Wrapper[Z,vpr.Exp,T] = func(this)
      def wrap(in: vpr.Exp): T = _wrap(in)
    }

    case class AllWrapper[X,T](decls: Vector[vpr.LocalVarDecl],
                               param: X,
                               triggers: Vector[vpr.Trigger])
                              (val _post: vpr.Exp => T, val _pre: vpr.Exp => vpr.Exp)
                               extends Wrapper[X, vpr.Exp, T] {

      def combine[Z](func: Wrapper[X,vpr.Exp,T] => Wrapper[Z, vpr.Exp, T]): Wrapper[Z, vpr.Exp, T] = func(this) match {
        case w @ UnitWrapper(ps) => AllWrapper(decls, ps, triggers)(w.wrap, identity)
        case w @ AllWrapper(ds,ps,ts) => AllWrapper(decls ++: ds, ps, ts)(w._post, w._pre)
      }

      def wrap(in: vpr.Exp): T =
        _post(
          vpr.Forall(
            variables = decls,
            triggers = triggers,
            exp = _pre(in)
          )()
        )
    }
  }

  trait SequenceStabelizeVersionedSelector[T] extends TranslatorUtils.VersionedSelector[T] {
    sequenceStabilizeSubject.addObserver(this) // TODO: probably a very bad idea -> data races
  }
}
