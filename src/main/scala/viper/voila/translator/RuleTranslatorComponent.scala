/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.voila.frontend._
import viper.voila.reporting.UseAtomicError
import viper.silver.{ast => vpr}
import viper.silver.verifier.{errors => vprerr, reasons => vprrea}

trait RuleTranslatorComponent { this: PProgramToViperTranslator =>
  private var lastPreUpdateRegionLabel: vpr.Label = _
  private var preUpdateRegionCounter = 0

  def freshPreUpdateRegionLabel(): vpr.Label = {
    preUpdateRegionCounter += 1

    val label =
      vpr.Label(
        s"pre_region_update_$preUpdateRegionCounter",
        Vector.empty
      )()

    lastPreUpdateRegionLabel = label

    label
  }

  // TODO: Unify fresh label code

  private var lastPreUseAtomicLabel: vpr.Label = _
  private var preUseAtomicCounter = 0

  def freshPreUseAtomicLabel(): vpr.Label = {
    preUseAtomicCounter += 1

    val label =
      vpr.Label(
        s"pre_use_atomic_$preUseAtomicCounter",
        Vector.empty
      )()

    lastPreUseAtomicLabel = label

    label
  }

  def translate(makeAtomic: PMakeAtomic): vpr.Stmt = {
    val regionArgs = makeAtomic.regionPredicate.arguments
    val regionId = regionArgs.head.asInstanceOf[PIdnExp].id

    val (region, vprRegionArgs, None) =
      getAndTranslateRegionPredicateDetails(makeAtomic.regionPredicate)

    val regionType = semanticAnalyser.typ(region.state)
    val vprRegionIdArg = vprRegionArgs.head

    val guard =
      semanticAnalyser.entity(makeAtomic.guard.guard).asInstanceOf[GuardEntity]
                      .declaration

    val inhaleDiamond =
      vpr.Inhale(diamondAccess(translateUseOf(makeAtomic.guard.regionId)))()

    val exhaleGuard =
      vpr.Exhale(guardAccessIfNotDuplicable(makeAtomic.guard))()

    val interference = semanticAnalyser.interferenceSpecifications(makeAtomic).head
    // TODO: Actually use computed interference

    val havoc1 = havocSingleRegionInstance(region, regionArgs)
    val havoc2 = havocSingleRegionInstance(region, regionArgs)

    val ruleBody = translate(makeAtomic.body)

    val vprAtomicityContextX = atomicityContextVariable(regionId).localVar

    val checkUpdatePermitted = {
      val checkFrom =
        vpr.Assert(
          vpr.AnySetContains(
            stepFromLocation(vprRegionIdArg, regionType),
            vprAtomicityContextX
          )()
        )()

      val checkTo =
        vpr.Assert(
          vpr.AnySetContains(
            stepToLocation(vprRegionIdArg, regionType),
            vpr.FuncApp(
              guardTransitiveClosureFunction(guard, region),
              Vector(vprRegionIdArg, stepFromLocation(vprRegionIdArg, regionType))
            )()
          )()
        )()

      vpr.Seqn(
        Vector(
          checkFrom,
          checkTo),
        Vector.empty
      )()
    }

    val vprRegionState =
      vpr.FuncApp(
        regionStateFunction(region),
        vprRegionArgs
      )()

    val assumeCurrentStateIsStepTo =
      vpr.Inhale(
        vpr.EqCmp(
          vprRegionState,
          stepToLocation(vprRegionIdArg, regionType)
        )()
      )()

    val assumeOldStateWasStepFrom =
      vpr.Inhale(
        vpr.EqCmp(
          vpr.Old(vprRegionState)(),
          stepFromLocation(vprRegionIdArg, regionType)
        )()
      )()

    val inhaleGuard = vpr.Inhale(exhaleGuard.exp)()

    val exhaleTrackingResource = {
      val stepFrom = stepFromAccess(vprRegionIdArg, regionType)
      val stepTo = stepToAccess(vprRegionIdArg, regionType)

      vpr.Exhale(
        vpr.And(
          stepFrom,
          stepTo
        )()
      )()
    }

    val result =
      vpr.Seqn(
        Vector(
          inhaleDiamond,
          exhaleGuard,
          havoc1,
          ruleBody,
          checkUpdatePermitted,
          havoc2,
          BLANK_LINE,
          assumeCurrentStateIsStepTo,
          assumeOldStateWasStepFrom,
          inhaleGuard,
          exhaleTrackingResource),
        Vector.empty
      )()

    surroundWithSectionComments(makeAtomic.statementName, result)
  }

  def translate(updateRegion: PUpdateRegion): vpr.Stmt = {
    val (region, vprRegionArgs, None) =
      getAndTranslateRegionPredicateDetails(updateRegion.regionPredicate)

    val regionType = semanticAnalyser.typ(region.state)
    val vprRegionIdArg = vprRegionArgs.head

    val exhaleDiamond =
      vpr.Exhale(diamondAccess(vprRegionIdArg))()

    val label = freshPreUpdateRegionLabel()

    val unfoldRegionPredicate =
      vpr.Unfold(regionPredicateAccess(region, vprRegionArgs))()

    val ruleBody = translate(updateRegion.body)

    val foldRegionPredicate =
      vpr.Fold(regionPredicateAccess(region, vprRegionArgs))()

    val currentState =
      vpr.FuncApp(
        regionStateFunction(region),
        vprRegionArgs
      )()

    val oldState =
      vpr.LabelledOld(
        currentState,
        lastPreUpdateRegionLabel.name
      )()

    val stateChanged = vpr.NeCmp(currentState, oldState)()

    val obtainTrackingResource = {
      val stepFrom = stepFromAccess(vprRegionIdArg, regionType)
      val stepTo = stepToAccess(vprRegionIdArg, regionType)

      val inhaleFromTo =
        vpr.Inhale(
          vpr.And(
            stepFrom,
            stepTo
          )()
        )()

      val initFrom = vpr.FieldAssign(stepFrom.loc, oldState)()
      val initTo = vpr.FieldAssign(stepTo.loc, currentState)()

      vpr.Seqn(
        Vector(
          inhaleFromTo,
          initFrom,
          initTo),
        Vector.empty
      )()
    }

    val inhaleDiamond = vpr.Inhale(diamondAccess(vprRegionIdArg))()

    val postRegionUpdate =
      vpr.If(
        stateChanged,
        obtainTrackingResource,
        vpr.Seqn(Vector(inhaleDiamond), Vector.empty)()
      )()

    val result =
      vpr.Seqn(
        Vector(
          exhaleDiamond,
          label,
          unfoldRegionPredicate,
          ruleBody,
          foldRegionPredicate,
          postRegionUpdate),
        Vector.empty
      )()

    surroundWithSectionComments(updateRegion.statementName, result)
  }

  def translate(useAtomic: PUseAtomic): vpr.Stmt = {
    val (region, vprRegionArgs, None) =
      getAndTranslateRegionPredicateDetails(useAtomic.regionPredicate)

    val vprRegionIdArg = vprRegionArgs.head

    val guard =
      semanticAnalyser.entity(useAtomic.guard.guard).asInstanceOf[GuardEntity]
                      .declaration

    val label = freshPreUseAtomicLabel()

    val checkGuard =
      vpr.Assert(guardAccessIfNotDuplicable(useAtomic.guard))()

    errorBacktranslator.addErrorTransformer {
      case vprerr.AssertFailed(`checkGuard`, _: vprrea.InsufficientPermission, _) =>
        UseAtomicError(useAtomic, s"Guard ${useAtomic.guard} might not be available")
    }

    val unfoldRegionPredicate =
      vpr.Unfold(regionPredicateAccess(region, vprRegionArgs))()

    errorBacktranslator.addErrorTransformer {
      case vprerr.UnfoldFailed(`unfoldRegionPredicate`, _: vprrea.InsufficientPermission, _) =>
        UseAtomicError(useAtomic, s"Region predicate ${useAtomic.regionPredicate} might not be available")
    }

    val ruleBody = translate(useAtomic.body)

    val foldRegionPredicate =
      vpr.Fold(regionPredicateAccess(region, vprRegionArgs))()

    val currentState =
      vpr.FuncApp(
        regionStateFunction(region),
        vprRegionArgs
      )()

    val oldState =
      vpr.LabelledOld(
        currentState,
        lastPreUseAtomicLabel.name
      )()

    val stateChangePermitted =
      vpr.Exhale(
        vpr.AnySetContains(
          currentState,
          vpr.FuncApp(
            guardTransitiveClosureFunction(guard, region),
            Vector(vprRegionIdArg, oldState)
          )()
        )()
      )()

    errorBacktranslator.addErrorTransformer {
      case vprerr.ExhaleFailed(`stateChangePermitted`, _: vprrea.AssertionFalse, _) =>
        UseAtomicError(useAtomic, s"Performed state change not permitted")
    }

    val havocs =
      vpr.Seqn(
        tree.root.regions.map(region => havocAllRegionsInstances(region)),
        Vector.empty
      )()

    val result =
      vpr.Seqn(
        Vector(
          label,
          checkGuard,
          unfoldRegionPredicate,
          ruleBody,
          foldRegionPredicate,
          stateChangePermitted,
          havocs),
              /* TODO: Havocking after use-atomic is in general too eager.
               *       Instead, we want to havoc if an atomic-triple-rule is used
               *       in the proof of a non-atomic triple.
               *       See also the comments in the manual encoding outline_translation-capslock.vpr.
               */
        Vector.empty
      )()

    surroundWithSectionComments(useAtomic.statementName, result)
  }

  def translate(openRegion: POpenRegion): vpr.Stmt = {
    val (region, vprRegionArgs, None) =
      getAndTranslateRegionPredicateDetails(openRegion.regionPredicate)

    val unfoldRegionPredicate =
      vpr.Unfold(regionPredicateAccess(region, vprRegionArgs))()

    val ruleBody = translate(openRegion.body)

    val foldRegionPredicate =
      vpr.Fold(regionPredicateAccess(region, vprRegionArgs))()

    val result =
      vpr.Seqn(
        Vector(
          unfoldRegionPredicate,
          ruleBody,
          foldRegionPredicate),
        Vector.empty
      )()

    surroundWithSectionComments(openRegion.statementName, result)
  }

  protected def guardAccessIfNotDuplicable(guardExp: PGuardExp): vpr.Exp = {
    val guardDecl = semanticAnalyser.entity(guardExp.guard).asInstanceOf[GuardEntity]
                                    .declaration

    guardDecl.modifier match {
      case PUniqueGuard() => translate(guardExp)
      case PDuplicableGuard() => vpr.TrueLit()()
    }
  }
}
