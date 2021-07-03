/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.voila.frontend._
import viper.voila.reporting._
import viper.silver.{ast => vpr}
import viper.silver.verifier.{errors => vprerr, reasons => vprrea}

trait RuleTranslatorComponent { this: PProgramToViperTranslator =>
  protected var currentlyOpenRegions: List[(PRegion, Vector[PExpression], vpr.Label)] = List.empty
    /* Important: use as a stack! */

  def translate(makeAtomic: PMakeAtomic): vpr.Stmt = {
    val regionArgs = makeAtomic.regionPredicate.arguments
    val regionId = regionArgs.head.asInstanceOf[PIdnExp].id

    val (region, regionInArgs, _, regionOutArgsConstraints) =
      getAndTranslateRegionPredicateDetails(makeAtomic.regionPredicate)

    assert(
      regionOutArgsConstraints.isEmpty,
       "Using-clauses expect region assertions without out-arguments, but got " +
      s"${makeAtomic.regionPredicate} at ${makeAtomic.regionPredicate.position}")

    val regionType = semanticAnalyser.typ(region.state)
    val vprRegionIdArg = regionInArgs.head

    if (makeAtomic.posts.isEmpty) {
      val storeCurrentLvl = AtomicityContextLevelManager.registerRegionExp(region, regionInArgs)

      val inhaleDiamond =
        vpr.Inhale(diamondAccess(translateUseOf(regionId)))()

      val guard = viper.silicon.utils.ast.BigAnd(makeAtomic.guards map translate)

      val exhaleGuard =
        vpr.Exhale(guard)().withSource(makeAtomic.guards.head)

      errorBacktranslator.addErrorTransformer {
        case e: vprerr.ExhaleFailed if e causedBy exhaleGuard =>
          MakeAtomicError(makeAtomic, InsufficientGuardPermissionError(makeAtomic.guards.head))
      }

      val regionPredicate =
        vpr.PredicateAccessPredicate(
          vpr.PredicateAccess(
            args = regionInArgs,
            predicateName = region.id.name
          )(),
          vpr.FullPerm()()
        )()

      val exhaleRegionPredicate = vpr.Exhale(regionPredicate)().withSource(makeAtomic)

      errorBacktranslator.addErrorTransformer {
        case e: vprerr.ExhaleFailed if e causedBy exhaleRegionPredicate =>
          MakeAtomicError(makeAtomic, InsufficientRegionPermissionError(makeAtomic.regionPredicate))
      }

      val (preFrameExhales, postFrameInhales) = completeFrame

      val inhaleRegionPredicate = vpr.Inhale(regionPredicate)()

      val contextCheck = checkAtomicityNotYetCaptured(region, regionInArgs)

      errorBacktranslator.addErrorTransformer {
        case e: vprerr.AssertFailed if e causedBy contextCheck =>
          MakeAtomicError(makeAtomic, RegionAtomicityContextTrackingError(makeAtomic.regionPredicate))
      }

      val assignContext = assignAtomicityContext(region, regionInArgs)

      val guardArgEvaluationLabel = freshLabel("guard_arg_eval")

      val havoc1 = stabilizeSingleInstances("before atomic", (region, regionInArgs)) // used to constrain state of updated region

      val ruleBody = translate(makeAtomic.body)

      val havocSingleInstance = havocSingleInstances("after atomic", (region, regionInArgs))

      val vprAtomicityContextX = atomicityContextFunctions.application(region, regionInArgs)

      val vprStepFrom =
        stepFromLocation(vprRegionIdArg, regionType).withSource(regionId)

      val vprStepTo =
        stepToLocation(vprRegionIdArg, regionType).withSource(regionId)

      val checkUpdatePermitted = {
        val vprStepFromAllowed =
          vpr.AnySetContains(
            vprStepFrom,
            vprAtomicityContextX
          )().withSource(makeAtomic)

        val vprCheckFrom =
          vpr.Assert(vprStepFromAllowed)().withSource(makeAtomic)

        errorBacktranslator.addErrorTransformer {
          case e @ vprerr.AssertFailed(_, reason: vprrea.InsufficientPermission, _)
            if (e causedBy vprCheckFrom) && (reason causedBy vprStepFrom) =>

            MakeAtomicError(makeAtomic)
              .dueTo(InsufficientTrackingResourcePermissionError(makeAtomic.regionPredicate, regionId))
              .dueTo(hintAtEnclosingLoopInvariants(regionId))
              .dueTo(AdditionalErrorClarification("This could be related to issue #8", regionId))

          case e @ vprerr.AssertFailed(_, reason: vprrea.AssertionFalse, _)
            if (e causedBy vprCheckFrom) && (reason causedBy vprStepFromAllowed) =>

            MakeAtomicError(makeAtomic)
              .dueTo(IllegalRegionStateChangeError(makeAtomic.body))
              .dueTo(AdditionalErrorClarification(
                "In particular, it cannot be shown that the region is transitioned from a " +
                  "state that is compatible with the procedure's interference specification",
                regionId))
              .dueTo(hintAtEnclosingLoopInvariants(regionId))
        }

        val vprCheckTo =
          regionStateChangeAllowedByGuard(
            region,
            regionInArgs,
            makeAtomic.guards, /* FIXME: only temporal placeholder, guard is going to be a vector itself */
            vprStepFrom,
            vprStepTo,
            guardArgEvaluationLabel
          ).withSource(makeAtomic)

        errorBacktranslator.addErrorTransformer {
          case e: vprerr.AssertFailed if e causedBy vprCheckTo =>
            MakeAtomicError(makeAtomic)
              .dueTo(IllegalRegionStateChangeError(makeAtomic.guards.head))
              .dueTo(hintAtEnclosingLoopInvariants(regionId))
        }

        vpr.Seqn(
          Vector(
            vprCheckFrom,
            vprCheckTo),
          Vector.empty
        )()
      }

      val vprRegionState =
        vpr.FuncApp(
          regionStateFunction(region),
          regionInArgs
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

      val inhaleGuard = vpr.Inhale(guard)()

      val exhaleTrackingResource = {
        val stepFrom =
          stepFromAccess(vprRegionIdArg, regionType).withSource(makeAtomic.regionPredicate)

        val stepTo =
          stepToAccess(vprRegionIdArg, regionType).withSource(makeAtomic.regionPredicate)

        val exhale =
          vpr.Exhale(
            vpr.And(
              stepFrom,
              stepTo
            )()
          )().withSource(makeAtomic.regionPredicate)

        errorBacktranslator.addErrorTransformer {
          case e: vprerr.ExhaleFailed if e causedBy exhale =>
            MakeAtomicError(makeAtomic)
              .dueTo(InsufficientTrackingResourcePermissionError(makeAtomic.regionPredicate, regionId))
              .dueTo(hintAtEnclosingLoopInvariants(regionId))
        }

        exhale
      }

      val deselectContext = deselectAtomicityContext(region, regionInArgs)

      AtomicityContextLevelManager.removeLastRegionExp()

      val result =
        vpr.Seqn(
          Vector(
            guardArgEvaluationLabel,
            exhaleGuard,
            exhaleRegionPredicate,
            preFrameExhales,
            inhaleRegionPredicate,
            inhaleDiamond,
            storeCurrentLvl,
            contextCheck,
            assignContext,
            havoc1,
            ruleBody,
            checkUpdatePermitted,
            havocSingleInstance,
            BLANK_LINE,
            assumeCurrentStateIsStepTo,
            assumeOldStateWasStepFrom,
            inhaleGuard,
            exhaleTrackingResource,
            deselectContext,
            postFrameInhales),
          Vector.empty
        )()

      surroundWithSectionComments(makeAtomic.statementName, result)
    } else {

      val guardArgEvaluationLabel = freshLabel("guard_arg_eval")

      val guard = viper.silicon.utils.ast.BigAnd(makeAtomic.guards map translate)

      val regionPredicate =
        vpr.PredicateAccessPredicate(
          vpr.PredicateAccess(
            args = regionInArgs,
            predicateName = region.id.name
          )(),
          vpr.FullPerm()()
        )()

      val preMakeAtomic: Vector[vpr.Stmt] = {

        val exhaleGuard =
          vpr.Exhale(guard)().withSource(makeAtomic.guards.head)

        errorBacktranslator.addErrorTransformer {
          case e: vprerr.ExhaleFailed if e causedBy exhaleGuard =>
            MakeAtomicError(makeAtomic, InsufficientGuardPermissionError(makeAtomic.guards.head))
        }

        val exhaleRegionPredicate = vpr.Exhale(regionPredicate)().withSource(makeAtomic)

        errorBacktranslator.addErrorTransformer {
          case e: vprerr.ExhaleFailed if e causedBy exhaleRegionPredicate =>
            MakeAtomicError(makeAtomic, InsufficientRegionPermissionError(makeAtomic.regionPredicate))
        }

        val stabilizeFrame = stabilizeAllInstances("stabilizing frame before make-atomic")

        val storeCurrentLvl = AtomicityContextLevelManager.registerRegionExp(region, regionInArgs)

        val contextCheck = checkAtomicityNotYetCaptured(region, regionInArgs)

        errorBacktranslator.addErrorTransformer {
          case e: vprerr.AssertFailed if e causedBy contextCheck =>
            MakeAtomicError(makeAtomic, RegionAtomicityContextTrackingError(makeAtomic.regionPredicate))
        }

        val assignContext = assignAtomicityContext(region, regionInArgs)

        Vector(
          exhaleGuard,
          exhaleRegionPredicate,
          stabilizeFrame,
          storeCurrentLvl,
          contextCheck,
          assignContext
        )
      }

      val inhaleSkolemizationFunctionFootprints =
        vpr.Inhale(
          viper.silicon.utils.ast.BigAnd(
            /* TODO: Would benefit from an optimisation similar to issue #47 */
            tree.root.regions map (region =>
              actionSkolemizationFunctionFootprintAccess(region.id.name)))
        )()

      val initializeFootprints = initializingFunctions.flatMap(tree.root.regions map _)

      val preAtomicityLabel = freshLabel("preWhile")

      val atomicityConstraints = tree.root.regions map (region => {
        val wrapper = atomicityContextAllWrapper(region, preAtomicityLabel)
        val constraint = atomicityContextEqualsOldConstraint(region, preAtomicityLabel)
        atomicityContextFunctions.refSelect(region, constraint, preAtomicityLabel)(wrapper)
      })

      val previousLvlToken = LevelManager.getCurrentLevelToken

      val vprPureBody = {
        val inhaleRegionPredicate = vpr.Inhale(regionPredicate)()
        val inhaleDiamond =
          vpr.Inhale(diamondAccess(translateUseOf(regionId)))()
        val havoc1 = stabilizeSingleInstances("before atomic", (region, regionInArgs)) // used to constrain state of updated region

        val ruleBody = translate(makeAtomic.body)

        val havocSingleInstance = havocSingleInstances("after atomic", (region, regionInArgs))

        val checkUpdatePermitted = {
          val vprAtomicityContextX = atomicityContextFunctions.application(region, regionInArgs)

          val vprStepFrom =
            stepFromLocation(vprRegionIdArg, regionType).withSource(regionId)

          val vprStepTo =
            stepToLocation(vprRegionIdArg, regionType).withSource(regionId)

          val vprStepFromAllowed =
            vpr.AnySetContains(
              vprStepFrom,
              vprAtomicityContextX
            )().withSource(makeAtomic)

          val vprCheckFrom =
            vpr.Assert(vprStepFromAllowed)().withSource(makeAtomic)

          errorBacktranslator.addErrorTransformer {
            case e @ vprerr.AssertFailed(_, reason: vprrea.InsufficientPermission, _)
              if (e causedBy vprCheckFrom) && (reason causedBy vprStepFrom) =>

              MakeAtomicError(makeAtomic)
                .dueTo(InsufficientTrackingResourcePermissionError(makeAtomic.regionPredicate, regionId))
                .dueTo(hintAtEnclosingLoopInvariants(regionId))
                .dueTo(AdditionalErrorClarification("This could be related to issue #8", regionId))

            case e @ vprerr.AssertFailed(_, reason: vprrea.AssertionFalse, _)
              if (e causedBy vprCheckFrom) && (reason causedBy vprStepFromAllowed) =>

              MakeAtomicError(makeAtomic)
                .dueTo(IllegalRegionStateChangeError(makeAtomic.body))
                .dueTo(AdditionalErrorClarification(
                  "In particular, it cannot be shown that the region is transitioned from a " +
                    "state that is compatible with the procedure's interference specification",
                  regionId))
                .dueTo(hintAtEnclosingLoopInvariants(regionId))
          }

          val vprCheckTo =
            regionStateChangeAllowedByGuard(
              region,
              regionInArgs,
              makeAtomic.guards, /* FIXME: only temporal placeholder, guard is going to be a vector itself */
              vprStepFrom,
              vprStepTo,
              guardArgEvaluationLabel
            ).withSource(makeAtomic)

          errorBacktranslator.addErrorTransformer {
            case e: vprerr.AssertFailed if e causedBy vprCheckTo =>
              MakeAtomicError(makeAtomic)
                .dueTo(IllegalRegionStateChangeError(makeAtomic.guards.head))
                .dueTo(hintAtEnclosingLoopInvariants(regionId))
          }

          vpr.Seqn(
            Vector(
              vprCheckFrom,
              vprCheckTo),
            Vector.empty
          )()
        }

        val vprRegionState =
          vpr.FuncApp(
            regionStateFunction(region),
            regionInArgs
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

        val inhaleGuard = vpr.Inhale(guard)()

        val exhaleTrackingResource = {
          val stepFrom =
            stepFromAccess(vprRegionIdArg, regionType).withSource(makeAtomic.regionPredicate)

          val stepTo =
            stepToAccess(vprRegionIdArg, regionType).withSource(makeAtomic.regionPredicate)

          val exhale =
            vpr.Exhale(
              vpr.And(
                stepFrom,
                stepTo
              )()
            )().withSource(makeAtomic.regionPredicate)

          errorBacktranslator.addErrorTransformer {
            case e: vprerr.ExhaleFailed if e causedBy exhale =>
              MakeAtomicError(makeAtomic)
                .dueTo(InsufficientTrackingResourcePermissionError(makeAtomic.regionPredicate, regionId))
                .dueTo(hintAtEnclosingLoopInvariants(regionId))
          }

          exhale
        }

        Vector(
          inhaleRegionPredicate,
          inhaleDiamond,
          havoc1,
          ruleBody,
          havocSingleInstance,
          checkUpdatePermitted,
          assumeCurrentStateIsStepTo,
          assumeOldStateWasStepFrom,
          inhaleGuard,
          exhaleTrackingResource
        )
      }

      /* This assertion should never fail, because levels are always restored after an action
       * that changes the level
       */
      val levelCheck = vpr.Assert(LevelManager.compareToOldLevel(previousLvlToken))()

      val loopVarDecl = vpr.LocalVarDecl(freshIdentifier("loopVar"), vpr.Bool)()
      val loopVar = loopVarDecl.localVar

      val setLoopVarTrue = vpr.LocalVarAssign(loopVar, vpr.TrueLit()())()

      val setLoopVarFalse = vpr.LocalVarAssign(loopVar, vpr.FalseLit()())()

      val vprBody =
        vpr.Seqn(
          inhaleSkolemizationFunctionFootprints +:
            initializeFootprints ++:
            atomicityConstraints ++:
            (vprPureBody :+ levelCheck :+ setLoopVarFalse),
          Vector.empty
        )()

      val vprInvs = {
        makeAtomic.posts.map { post =>
          val inv = vpr.Implies(
            vpr.Not(loopVar)(),
            translate(post.assertion)
          )().withSource(makeAtomic, overwrite = true)

          val ebt = this.errorBacktranslator
          errorBacktranslator.addErrorTransformer {
            case e: vprerr.LoopInvariantNotPreserved if e causedBy inv =>
              PostconditionError(post.assertion, ebt.translate(e.reason))
          }

          inv
        }
      }

      var vprWhile =
        vpr.While(
          cond = loopVar,
          invs = vprInvs,
          body = vprBody
        )()

      vprWhile = vprWhile.withSource(makeAtomic)



      val assignOldLevel = LevelManager.assignOldLevel(previousLvlToken)

      val deselectContext = deselectAtomicityContext(region, regionInArgs)
      AtomicityContextLevelManager.removeLastRegionExp()

      val total = vpr.Seqn(
        preMakeAtomic ++ Vector(preAtomicityLabel, setLoopVarTrue, vprWhile, assignOldLevel, deselectContext),
        Vector(loopVarDecl)
      )()

      surroundWithSectionComments(makeAtomic.statementName, total)
    }


  }

  def translate(updateRegion: PUpdateRegion): vpr.Stmt = {
    val regionArgs = updateRegion.regionPredicate.arguments
    val regionId = regionArgs.head.asInstanceOf[PIdnExp].id

    val (region, vprInArgs, _, vprOutArgsConstraints) =
      getAndTranslateRegionPredicateDetails(updateRegion.regionPredicate)

      assert(
        vprOutArgsConstraints.isEmpty,
         "Using-clauses expect region assertions without out-arguments, but got " +
        s"${updateRegion.regionPredicate} at ${updateRegion.regionPredicate.position}")

    val regionType = semanticAnalyser.typ(region.state)
    val vprRegionId = vprInArgs.head

    val exhaleDiamond =
      vpr.Exhale(diamondAccess(vprRegionId))().withSource(updateRegion.regionPredicate)

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.ExhaleFailed if e causedBy exhaleDiamond =>
        UpdateRegionError(updateRegion)
          .dueTo(InsufficientDiamondResourcePermissionError(updateRegion.regionPredicate, regionId))
          .dueTo(hintAtEnclosingLoopInvariants(regionId))
    }

    val exhaleAtomicityTracking =
      deselectAtomicityContext(region, vprInArgs).withSource(updateRegion.regionPredicate)

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.ExhaleFailed if e causedBy exhaleAtomicityTracking =>
        UpdateRegionError(updateRegion)
          .dueTo(InsufficientRegionAtomicityContextTrackingError(updateRegion.regionPredicate))
    }

    val label = freshLabel("pre_region_update")

    val levelCheck = vpr.Assert(LevelManager.levelHigherThanOccurringRegionLevels(updateRegion.regionPredicate))()

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.AssertFailed if e causedBy levelCheck =>
        UpdateRegionError(updateRegion, InspectLevelTooHighError(updateRegion.regionPredicate))
    }


    val levelToken = LevelManager.getCurrentLevelToken
    val newLevelAssignment = LevelManager.assignLevel(vprInArgs(1))

    val unfoldRegionPredicate =
      vpr.Unfold(regionPredicateAccess(region, vprInArgs))().withSource(updateRegion.regionPredicate)

    val tranitionInterferenceContext = linkInterferenceContext(region, vprInArgs)

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.UnfoldFailed if e causedBy unfoldRegionPredicate =>
        UpdateRegionError(updateRegion, InsufficientRegionPermissionError(updateRegion.regionPredicate))
    }

    val havocRegionCopies = {
      val regionPredicate =
        vpr.PredicateAccessPredicate(
          vpr.PredicateAccess(
            args = vprInArgs,
            predicateName = region.id.name
          )(),
          vpr.CurrentPerm(
            vpr.PredicateAccess(
              args = vprInArgs,
              predicateName = region.id.name
            )()
          )()
        )()

      vpr.Exhale(regionPredicate)()
      // havocSingleInstances(s"before ${updateRegion.statementName}@${updateRegion.lineColumnPosition}", (region, vprInArgs))
    }

    val ruleBody = translate(updateRegion.body)

    val foldRegionPredicate =
      vpr.Fold(regionPredicateAccess(region, vprInArgs))().withSource(updateRegion.regionPredicate)

    val ebt = this.errorBacktranslator // TODO: Should not be necessary!!!!!
    errorBacktranslator.addErrorTransformer {
      case e: vprerr.FoldFailed if e causedBy foldRegionPredicate =>
        UpdateRegionError(updateRegion, ebt.translate(e.reason))
    }

    val currentState =
      vpr.FuncApp(
        regionStateFunction(region),
        vprInArgs
      )()

    val oldState =
      vpr.LabelledOld(
        currentState,
        label.name
      )()

    val stateChanged = updateRegion.cond match {
      case Some(c) => vpr.Or(vpr.NeCmp(currentState, oldState)(), translate(c))()
      case None => vpr.NeCmp(currentState, oldState)()
    }

    val obtainTrackingResource = {
      val stepFrom = stepFromAccess(vprRegionId, regionType)
      val stepTo = stepToAccess(vprRegionId, regionType)

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

    val inhaleDiamond = vpr.Inhale(diamondAccess(vprRegionId))()

    val postRegionUpdate =
      vpr.If(
        stateChanged,
        obtainTrackingResource,
        vpr.Seqn(Vector(inhaleDiamond), Vector.empty)()
      )()

    val inhaleAtomicityTracking = assignOldAtomicityContext(region, vprInArgs, label)

    val oldLevelAssignment = LevelManager.assignOldLevel(levelToken)

    val result =
      vpr.Seqn(
        Vector(
          exhaleDiamond,
          label,
          levelCheck,
          newLevelAssignment,
          exhaleAtomicityTracking,
          unfoldRegionPredicate,
          tranitionInterferenceContext,
          havocRegionCopies,
          ruleBody,
          foldRegionPredicate,
          postRegionUpdate,
          inhaleAtomicityTracking,
          oldLevelAssignment),
        Vector.empty
      )()

    surroundWithSectionComments(updateRegion.statementName, result)
  }

  def translate(useAtomic: PUseAtomic): vpr.Stmt = {
    val (region, inArgs, outArgs) = getRegionPredicateDetails(useAtomic.regionPredicate)
    val vprInArgs = inArgs map translate

    assert(
      outArgs.isEmpty,
       "Using-clauses expect region assertions without out-arguments, but got " +
      s"${useAtomic.regionPredicate} at ${useAtomic.regionPredicate.position}")

    val preUseAtomicLabel = freshLabel("pre_use_atomic")

    val contextCheck = checkAtomicityNotYetCaptured(region, vprInArgs)

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.AssertFailed if e causedBy contextCheck =>
        UseAtomicError(useAtomic, RegionAtomicityContextTrackingError(useAtomic.regionPredicate))
    }

    val levelCheck = vpr.Assert(LevelManager.levelHigherThanOccurringRegionLevels(useAtomic.regionPredicate))()

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.AssertFailed if e causedBy levelCheck =>
        UseAtomicError(useAtomic, InspectLevelTooHighError(useAtomic.regionPredicate))
    }

    val levelToken = LevelManager.getCurrentLevelToken
    val newLevelAssignment = LevelManager.assignLevel(vprInArgs(1))

    val unfoldRegionPredicate =
      vpr.Unfold(regionPredicateAccess(region, vprInArgs))()

    val transitionInterferenceContext
    = linkInterferenceContext(region, vprInArgs)

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.UnfoldFailed if e causedBy unfoldRegionPredicate =>
        UseAtomicError(useAtomic, InsufficientRegionPermissionError(useAtomic.regionPredicate))
    }

    currentlyOpenRegions = (region, inArgs, preUseAtomicLabel) :: currentlyOpenRegions
    val ruleBody = translate(useAtomic.body)
    assert(currentlyOpenRegions.head == (region, inArgs, preUseAtomicLabel))
    currentlyOpenRegions = currentlyOpenRegions.tail

    val foldRegionPredicate =
      vpr.Fold(
        regionPredicateAccess(region, vprInArgs).withSource(useAtomic.regionPredicate)
      )().withSource(useAtomic.regionPredicate)

    /* TODO: Reconsider error messages - introduce dedicated "region closing failed" error? */

    val ebt = this.errorBacktranslator // TODO: Should not be necessary!!!!!
    errorBacktranslator.addErrorTransformer {
      case e: vprerr.FoldFailed if e causedBy foldRegionPredicate =>
        UseAtomicError(useAtomic)
          .dueTo(IllegalRegionStateChangeError(useAtomic.regionPredicate))
          .dueTo(AdditionalErrorClarification("In particular, closing the region at the end of the use-atomic block might fail", useAtomic.regionPredicate))
          .dueTo(ebt.translate(e.reason))
    }

    val guard = viper.silicon.utils.ast.BigAnd(useAtomic.guards map translate)

    /* Temporarily exhale the guard used in the use-atomic rule so that it is no longer held
     * when stabilising the frame.
     *
     * Note: The guard must be checked in any case! I.e. the check is independent of the
     * technical treatment of frame stabilisation.
     */
    // FIXME: currently head is taken as source
    val exhaleGuard = vpr.Exhale(guard)().withSource(useAtomic.guards.head)

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.ExhaleFailed if e causedBy exhaleGuard =>
        UseAtomicError(useAtomic, InsufficientGuardPermissionError(useAtomic.guards.head))
    }

    val inhaleGuard = vpr.Inhale(guard)()

    val havocRegionCopies = {
      val regionPredicate =
        vpr.PredicateAccessPredicate(
          vpr.PredicateAccess(
            args = vprInArgs,
            predicateName = region.id.name
          )(),
          vpr.CurrentPerm(
            vpr.PredicateAccess(
              args = vprInArgs,
              predicateName = region.id.name
            )()
          )()
        )()

      vpr.Exhale(regionPredicate)()
      // havocSingleInstances(s"before ${updateRegion.statementName}@${updateRegion.lineColumnPosition}", (region, vprInArgs))
    }

    val currentState =
      vpr.FuncApp(
        regionStateFunction(region),
        vprInArgs
      )()

    val oldState =
      vpr.LabelledOld(
        currentState,
        preUseAtomicLabel.name
      )()

    val stateChangeAllowed =
      regionStateChangeAllowedByGuard(
        region,
        vprInArgs,
        useAtomic.guards,
        oldState,
        currentState,
        preUseAtomicLabel
      ).withSource(useAtomic)

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.AssertFailed if e causedBy stateChangeAllowed =>
        UseAtomicError(useAtomic, IllegalRegionStateChangeError(useAtomic.body))

      case e: vprerr.AssertFailed if e causedBy stateChangeAllowed.exp =>
        UseAtomicError(useAtomic, IllegalRegionStateChangeError(useAtomic.body))
    }

    val oldLevelAssignment = LevelManager.assignOldLevel(levelToken)

    val result =
      vpr.Seqn(
        Vector(
          preUseAtomicLabel,
          contextCheck,
          levelCheck,
          newLevelAssignment,
          /* Note: Guard must be checked!
           * I.e. the check is independent of the technical treatment of frame stabilisation.
           */
          exhaleGuard,
          unfoldRegionPredicate,
          transitionInterferenceContext,
          inhaleGuard,
          havocRegionCopies,
          ruleBody,
          foldRegionPredicate,
          stateChangeAllowed,
          oldLevelAssignment),
        Vector.empty
      )()

    surroundWithSectionComments(useAtomic.statementName, result)
  }

  def translate(openRegion: POpenRegion): vpr.Stmt = {
    val (region, inArgs, outArgs) = getRegionPredicateDetails(openRegion.regionPredicate)
    val vprInArgs = inArgs map translate
    val preOpenLabel = freshLabel("pre_open_region")

    assert(
      outArgs.isEmpty,
       "Using-clauses expect region assertions without out-arguments, but got " +
      s"${openRegion.regionPredicate} at ${openRegion.regionPredicate.position}")

    val levelCheck = vpr.Assert(LevelManager.levelHigherThanOccurringRegionLevels(openRegion.regionPredicate))()

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.AssertFailed if e causedBy levelCheck =>
        OpenRegionError(openRegion, InspectLevelTooHighError(openRegion.regionPredicate))
    }

    val levelToken = LevelManager.getCurrentLevelToken
    val newLevelAssignment = LevelManager.assignLevel(vprInArgs(1))

    val unfoldRegionPredicate =
      vpr.Unfold(regionPredicateAccess(region, vprInArgs))()

    val tranitionInterferenceContext = linkInterferenceContext(region, vprInArgs)

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.UnfoldFailed if e causedBy unfoldRegionPredicate =>
        OpenRegionError(openRegion, InsufficientRegionPermissionError(openRegion.regionPredicate))
    }

    currentlyOpenRegions = (region, inArgs, preOpenLabel) :: currentlyOpenRegions
    val ruleBody = translate(openRegion.body)
    assert(currentlyOpenRegions.head == (region, inArgs, preOpenLabel))
    currentlyOpenRegions = currentlyOpenRegions.tail

    val foldRegionPredicate =
      vpr.Fold(regionPredicateAccess(region, vprInArgs))()

    val ebt = this.errorBacktranslator // TODO: Should not be necessary!!!!!
    errorBacktranslator.addErrorTransformer {
      case e: vprerr.FoldFailed if e causedBy foldRegionPredicate =>
        OpenRegionError(openRegion, ebt.translate(e.reason))
    }

    val currentState =
      vpr.FuncApp(
        regionStateFunction(region),
        vprInArgs
      )()

    val oldState =
      vpr.LabelledOld(
        currentState,
        preOpenLabel.name
      )()

    val stateUnchanged =
      vpr.Assert(
        vpr.EqCmp(
          currentState,
          oldState
        )()
      )()

    errorBacktranslator.addErrorTransformer {
      case e: vprerr.AssertFailed if e causedBy stateUnchanged =>
        OpenRegionError(openRegion, IllegalRegionStateChangeError(openRegion.body))
    }

    val oldLevelAssignment = LevelManager.assignOldLevel(levelToken)

    val result =
      vpr.Seqn(
        Vector(
          preOpenLabel,
          levelCheck,
          newLevelAssignment,
          unfoldRegionPredicate,
          tranitionInterferenceContext,
          ruleBody,
          foldRegionPredicate,
          stateUnchanged,
          oldLevelAssignment),
        Vector.empty
      )()

    surroundWithSectionComments(openRegion.statementName, result)
  }
}
