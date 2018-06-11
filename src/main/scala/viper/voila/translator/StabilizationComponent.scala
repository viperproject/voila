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
          stabilizeSingleInstance(region._1, region._2, preHavocLabel)))

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
          stabilizeAllInstances(region, preHavocLabel)))

    val result =
      vpr.Seqn(
        preHavocLabel +: stabilizeInstances,
        Vector.empty
      )()

    surroundWithSectionComments(stabilizationMessage, result)
  }

  private def beforeNonAtomic(): Unit = {
    sequenceStabilizeSubject.nextVersion
  }

  private def afterNonAtomic(preHavocLabel: vpr.Label): Unit = {

  }

  def nonAtomicStabilizeSingleInstances(reason: String, regions: (PRegion, Vector[vpr.Exp])*): vpr.Stmt = {
    val stabilizationMessage =
      s"Stabilising regions ${regions.map(_._1.id.name).mkString(",")} ($reason)"

    beforeNonAtomic()

    outputDebugInfo(stabilizationMessage)

    val preHavocLabel = freshLabel("pre_havoc")

    val stabilizeInstances =
      regions.map(region =>
        prependComment(
          s"Stabilising single instance of region ${region._1.id.name}",
          stabilizeAndInferContextSingleInstance(region._1, region._2, preHavocLabel)))

    val result =
      vpr.Seqn(
        preHavocLabel +: stabilizeInstances,
        Vector.empty
      )()

    afterNonAtomic(preHavocLabel)

    surroundWithSectionComments(stabilizationMessage, result)
  }

  def nonAtomicStabilizeAllInstances(reason: String): vpr.Stmt = {
    nonAtomicStabilizeAllInstances(reason, tree.root.regions : _*)
  }

  def nonAtomicStabilizeAllInstances(reason: String, regions: PRegion*): vpr.Stmt = {
    val stabilizationMessage =
      s"Stabilising regions ${regions.map(_.id.name).mkString(",")} ($reason)"

    beforeNonAtomic()

    outputDebugInfo(stabilizationMessage)

    val preHavocLabel = freshLabel("pre_havoc")

    val stabilizeInstances =
      regions.map(region =>
        prependComment(
          s"Stabilising all instances of region ${region.id.name}",
          stabilizeAndInferContextAllInstances(region, preHavocLabel)))

    val result =
      vpr.Seqn(
        preHavocLabel +: stabilizeInstances,
        Vector.empty
      )()

    afterNonAtomic(preHavocLabel)

    surroundWithSectionComments(stabilizationMessage, result)
  }

  def inferContextSingleInstances(reason: String, regions: (PRegion, Vector[vpr.Exp])*): vpr.Stmt = {
    val stabilizationMessage =
      s"Inferring interference Context ${regions.map(_._1.id.name).mkString(",")} ($reason)"

    sequenceStabilizeSubject.nextVersion

    outputDebugInfo(stabilizationMessage)

    val preHavocLabel = freshLabel("pre_havoc")

    val stabilizeInstances =
      regions.map(region =>
        prependComment(
          s"Inferring interference single instance of region ${region._1.id.name}",
          inferContextSingleInstance(region._1, region._2, preHavocLabel)))

    val result =
      vpr.Seqn(
        preHavocLabel +: stabilizeInstances,
        Vector.empty
      )()

    surroundWithSectionComments(stabilizationMessage, result)
  }

  def inferContextAllInstances(reason: String): vpr.Stmt = {
    inferContextAllInstances(reason, tree.root.regions : _*)
  }

  def inferContextAllInstances(reason: String, regions: PRegion*): vpr.Stmt = {
    val stabilizationMessage =
      s"Inferring interference context ${regions.map(_.id.name).mkString(",")} ($reason)"

    sequenceStabilizeSubject.nextVersion

    outputDebugInfo(stabilizationMessage)

    val preHavocLabel = freshLabel("pre_havoc")

    val stabilizeInstances =
      regions.map(region =>
        prependComment(
          s"Inferring interference all instances of region ${region.id.name}",
          inferContextAllInstances(region, preHavocLabel)))

    val result =
      vpr.Seqn(
        preHavocLabel +: stabilizeInstances,
        Vector.empty
      )()

    surroundWithSectionComments(stabilizationMessage, result)
  }

  private def stabilizeSingleInstance(region: PRegion,
                                       args: Vector[vpr.Exp],
                                       preHavocLabel: vpr.Label)
  : vpr.Stmt =
    stabilizeSingleRegion(region, singleWrapper(args), preHavocLabel)

  private def stabilizeAllInstances(region: PRegion,
                                    preHavocLabel: vpr.Label)
  : vpr.Stmt =
    stabilizeSingleRegion(region, regionAllWrapper(region, dfltPrePermissions(preHavocLabel)), preHavocLabel)

  private def stabilizeSingleRegion(region: PRegion,
                   wrapper: TranslatorUtils.BetterQuantifierWrapper.Wrapper,
                   preHavocLabel: vpr.Label)
  : vpr.Stmt = {
    val prePermissions = dfltPrePermissions(preHavocLabel)(_)
    val preRegionState = dfltPreRegionState(region, preHavocLabel)(_)
    val postRegionState = dfltPostRegionState(region)(_)
    val actionFilter = dfltActionFilter(region)(_)

    val resource = RegionStateFrontResourceWrapper(prePermissions)
    val constraint = possibleNextStateConstraint(region, actionFilter, preRegionState)

    resource.select(region, constraint)(wrapper)
  }

  private def stabilizeAndInferContextSingleInstance(region: PRegion,
                                                     args: Vector[vpr.Exp],
                                                     preHavocLabel: vpr.Label)
  : vpr.Stmt =
    stabilizeAndInferContextSingleRegion(region, singleWrapper(args), preHavocLabel)

  private def stabilizeAndInferContextAllInstances(region: PRegion,
                                                   preHavocLabel: vpr.Label)
  : vpr.Stmt =
    stabilizeAndInferContextSingleRegion(region, regionAllWrapper(region, dfltPrePermissions(preHavocLabel)), preHavocLabel)

  private def stabilizeAndInferContextSingleRegion(region: PRegion,
                   wrapper: TranslatorUtils.BetterQuantifierWrapper.Wrapper,
                   preHavocLabel: vpr.Label)
  : vpr.Stmt = {
    val prePermissions = dfltPrePermissions(preHavocLabel)(_)
    val preRegionState = dfltPreRegionState(region, preHavocLabel)(_)
    val postRegionState = dfltPostRegionState(region)(_)
    val actionFilter = dfltActionFilter(region)(_)

    val resource1 = interferenceSetFunctions
    val resource2 = RegionStateFrontResourceWrapper(prePermissions)
    val resource3 = interferenceReferenceFunctions

    val baseConstraint = possibleNextStateConstraint(region, actionFilter, preRegionState)
    val constraint1 = containsAllPossibleNextStatesConstraint(region, baseConstraint)
    val constraint2 = nextStateContainedInInference(region)
    val constraint3 = referencePointConstraint(region, prePermissions)

    vpr.Seqn(
      Vector(
        resource1.select(region, constraint1)(wrapper),
        resource2.select(region, constraint2)(wrapper),
        resource3.select(region, constraint3)(wrapper)
      ),
      Vector.empty
    )()
  }

  private def inferContextSingleInstance(region: PRegion,
                                                     args: Vector[vpr.Exp],
                                                     preHavocLabel: vpr.Label)
  : vpr.Stmt =
    inferContextSingleRegion(region, singleWrapper(args), preHavocLabel)

  private def inferContextAllInstances(region: PRegion,
                                                   preHavocLabel: vpr.Label)
  : vpr.Stmt =
    inferContextSingleRegion(region, regionAllWrapper(region, dfltPrePermissions(preHavocLabel)), preHavocLabel)

  private def inferContextSingleRegion(region: PRegion,
                                       wrapper: TranslatorUtils.BetterQuantifierWrapper.Wrapper,
                                       preHavocLabel: vpr.Label)
  : vpr.Stmt = {
    val prePermissions = dfltPrePermissions(preHavocLabel)(_)
    val preRegionState = dfltPreRegionState(region, preHavocLabel)(_)
    val actionFilter = dfltActionFilter(region)(_)

    val resource1 = interferenceSetFunctions
    val resource2 = interferenceReferenceFunctions

    val baseConstraint = possibleNextStateConstraint(region, actionFilter, preRegionState)
    val constraint1 = containsAllPossibleNextStatesConstraint(region, baseConstraint)
    val constraint2 = referencePointConstraint(region, prePermissions)

    vpr.Seqn(
      Vector(
        resource1.select(region, constraint1)(wrapper),
        resource2.select(region, constraint2)(wrapper)
      ),
      Vector.empty
    )()
  }

  private def dfltActionFilter(region: PRegion)(action: PAction): Boolean = true

  private def dfltPostRegionState(region: PRegion)(args: Vector[vpr.Exp]): vpr.Exp =
    vpr.FuncApp(regionStateFunction(region), args)()

  private def dfltPreRegionState(region: PRegion, preLabel: vpr.Label)(args: Vector[vpr.Exp]): vpr.Exp =
    vpr.LabelledOld(vpr.FuncApp(regionStateFunction(region), args)(), preLabel.name)()

  private def dfltPrePermissions(preLabel: vpr.Label)(exp: vpr.Exp): vpr.Exp =
    vpr.LabelledOld(exp, preLabel.name)()



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

      val vprWrappedRegionAssertion = wrapper.wrapWithoutCondition(vprRegionAssertion)

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
        val vprAtomicityContext = atomicityContextFunctions.application(region, vprRegionArguments)
//          vpr.DomainFuncApp(
//            atomicityContextFunction(region),
//            vprRegionArguments,
//            Map.empty[vpr.TypeVar, vpr.Type]
//          )()

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


  trait SequenceStabelizeVersionedSelector[T] extends TranslatorUtils.VersionedSelector[T] {
    sequenceStabilizeSubject.addObserver(this) // TODO: probably a very bad idea -> data races
  }
}
