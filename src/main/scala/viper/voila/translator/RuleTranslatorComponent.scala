/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.voila.frontend._
import viper.silver.{ast => vpr}

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

  def translate(makeAtomic: PMakeAtomic): vpr.Stmt = {
    val region =
      semanticAnalyser.entity(makeAtomic.regionPredicate.predicate).asInstanceOf[RegionEntity]
                      .declaration

    val guard =
      semanticAnalyser.entity(makeAtomic.guard.guard).asInstanceOf[GuardEntity]
                      .declaration

    val regionType = semanticAnalyser.typ(region.state)

    val regionArgs =
      makeAtomic.regionPredicate.arguments.init

    val vprRegionIdArg +: vprRegularArgs :+ _ =
      makeAtomic.regionPredicate.arguments map translate

    val inhaleDiamond =
      vpr.Inhale(diamondAccess(translateUseOf(makeAtomic.guard.regionId)))()

    val exhaleGuard =
      vpr.Exhale(translate(makeAtomic.guard))()

    val interference = semanticAnalyser.interferenceSpecifications(makeAtomic).head

    val havoc =
      havocRegion(
        region,
        regionArgs,
        interference.set,
        tmpVar(semanticAnalyser.typ(region.state)).localVar)

    val ruleBody = translate(makeAtomic.body)

    val vprAtomicityContextX = translate(interference.set)

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
          checkTo)
      )()
    }

    val currentState =
      vpr.FuncApp(
        regionStateFunction(region),
        vprRegionIdArg +: vprRegularArgs
      )()

    val assumeStateIsStepTo =
      vpr.Inhale(
        vpr.EqCmp(
          currentState,
          stepToLocation(vprRegionIdArg, regionType)
        )()
      )()

    val assumeInterferenceWasStepFrom =
      vpr.Inhale(
        vpr.EqCmp(
          translateUseOf(interference.variable),
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
          havoc,
          ruleBody,
          checkUpdatePermitted,
          havoc,
          BLANK_LINE,
          assumeStateIsStepTo,
          assumeInterferenceWasStepFrom,
          inhaleGuard,
          exhaleTrackingResource)
      )()

    surroundWithSectionComments(makeAtomic.statementName, result)
  }

  def translate(updateRegion: PUpdateRegion): vpr.Stmt = {
    val region =
      semanticAnalyser.entity(updateRegion.regionPredicate.predicate).asInstanceOf[RegionEntity]
                      .declaration

    val regionType = semanticAnalyser.typ(region.state)

    val vprRegionIdArg +: vprRegularArgs :+ _ =
      updateRegion.regionPredicate.arguments map translate

    val exhaleDiamond =
      vpr.Exhale(diamondAccess(vprRegionIdArg))()

    val label = freshPreUpdateRegionLabel()

    val unfoldRegionPredicate =
      vpr.Unfold(regionPredicateAccess(region, vprRegionIdArg +: vprRegularArgs))()

    val ruleBody = translate(updateRegion.body)

    val foldRegionPredicate =
      vpr.Fold(regionPredicateAccess(region, vprRegionIdArg +: vprRegularArgs))()

    val currentState =
      vpr.FuncApp(
        regionStateFunction(region),
        vprRegionIdArg +: vprRegularArgs
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
          initTo)
      )()
    }

    val inhaleDiamond = vpr.Inhale(diamondAccess(vprRegionIdArg))()

    val postRegionUpdate =
      vpr.If(
        stateChanged,
        obtainTrackingResource,
        inhaleDiamond
      )()

    val result =
      vpr.Seqn(
        Vector(
          exhaleDiamond,
          label,
          unfoldRegionPredicate,
          ruleBody,
          foldRegionPredicate,
          postRegionUpdate)
      )()

    surroundWithSectionComments(updateRegion.statementName, result)
  }
}
