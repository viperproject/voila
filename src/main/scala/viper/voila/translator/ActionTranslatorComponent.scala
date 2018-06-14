/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.{breakOut, mutable}
import viper.silver.{ast => vpr}
import viper.silver.verifier.{errors => vprerr, reasons => vprrea}
import viper.voila.backends.ViperAstUtils
import viper.voila.frontend._
import viper.voila.reporting.{FoldError, InsufficientGuardPermissionError, InsufficientRegionPermissionError, InterferenceError, PreconditionError, RegionStateError, UnfoldError}
import viper.voila.translator.TranslatorUtils.BetterQuantifierWrapper.WrapperExt
import viper.voila.translator.TranslatorUtils.{BetterQuantifierWrapper, Constraint}

trait ActionTranslatorComponent { this: PProgramToViperTranslator =>

  var USE_GUARD_SETS: Boolean = true

  private val guardPredicateCache =
    mutable.Map.empty[(PGuardDecl, PRegion), vpr.Predicate]

  protected val collectedActionSkolemizationFunctionFootprints =
  /* Maps regions to corresponding skolemization function footprints */
    mutable.Map.empty[String, vpr.Predicate]

  protected val collectedActionSkolemizationFunctions =
  /* Maps pairs of region and variable names to corresponding skolemization functions */
    mutable.Map.empty[(String, String), vpr.Function]

  def actionBinderRename(name: String): String = s"$$_action_$name" // TODO naming convention

  def actionSkolemizationFunctionFootprintName(regionName: String): String =
    s"${regionName}_sk_fp"

  def collectActionSkolemizationFunctionFootprint(region: PRegion): vpr.Predicate = {
    val footprintPredicate =
      vpr.Predicate(
        name = actionSkolemizationFunctionFootprintName(region.id.name),
        formalArgs = Vector.empty,
        body = None
      )()

    collectedActionSkolemizationFunctionFootprints += region.id.name -> footprintPredicate

    footprintPredicate
  }

  def actionSkolemizationFunctionFootprintAccess(regionName: String)
  : vpr.PredicateAccessPredicate = {

    vpr.PredicateAccessPredicate(
      vpr.PredicateAccess(
        args = Vector.empty,
        predicateName = actionSkolemizationFunctionFootprintName(regionName)
      )(),
      vpr.FullPerm()()
    )()
  }

  def actionSkolemizationFunctionName(regionName: String, variableName: String): String =
    s"${regionName}_sk_$variableName"

  def collectActionSkolemizationFunctions(region: PRegion): Vector[vpr.Function] = {
    val binders: Vector[PNamedBinder] = region.actions.flatMap(_.binders).distinct

    val vprSkolemizationFunctions =
      binders map (binder => {
        val vprFormalArguments = region.formalInArgs map translate
        val vprFootprint = actionSkolemizationFunctionFootprintAccess(region.id.name)

        val vprSkolemizationFunction =
          vpr.Function(
            name = actionSkolemizationFunctionName(region.id.name, binder.id.name),
            formalArgs = vprFormalArguments,
            typ = translate(semanticAnalyser.typeOfLogicalVariable(binder)),
            pres = Vector(vprFootprint),
            posts = Vector.empty,
            decs = None,
            body = None
          )()

        collectedActionSkolemizationFunctions +=
          (region.id.name, binder.id.name) -> vprSkolemizationFunction

        vprSkolemizationFunction
      })

    vprSkolemizationFunctions
  }


  def guardTriggerFunctionName(guard: PGuardDecl, region: PRegion): String =
    s"${guardPredicateName(guard, region)}_T"

  def guardTriggerFunction(guard: PGuardDecl, region: PRegion): Option[vpr.DomainFunc] = {
    val guardPred = guardPredicate(guard, region)

    if (guardPred.formalArgs.length <= 1) {
      None
    } else {
      Some(
        vpr.DomainFunc(
          name = guardTriggerFunctionName(guard, region),
          formalArgs = guardPred.formalArgs,
          typ = vpr.Bool
        )(domainName = regionStateTriggerFunctionsDomainName)
      )
    }
  }

  def guardTriggerFunction(guardPredicateName: String): Option[vpr.DomainFunc] = {
    val (guardName, regionName) = extractGuardAndRegionNameFromGuardPredicateName(guardPredicateName)
    val region = tree.root.regions.find(_.id.name == regionName).get
    val guard = region.guards.find(_.id.name == guardName).get

    guardTriggerFunction(guard, region)
  }

  def guardTriggerFunctionApplication(guardPredicateApplication: vpr.PredicateAccess)
  : Option[vpr.DomainFuncApp] =
    guardTriggerFunction(guardPredicateApplication.predicateName) map {
      guardTriggerFunc =>
        vpr.DomainFuncApp(
          func = guardTriggerFunc,
          args = guardPredicateApplication.args,
          typVarMap = Map.empty
        )()
    }

  def guardTriggerFunctionApplication(guard: PGuardDecl, args: Vector[vpr.Exp], region: PRegion)
  : Option[vpr.DomainFuncApp] =
    guardTriggerFunction(guard, region) map {
      guardTriggerFunc =>
        vpr.DomainFuncApp(
          func = guardTriggerFunc,
          args = args,
          typVarMap = Map.empty
        )()
    }

  def guardTriggerFunctionAxiom(guard: PGuardDecl, region: PRegion): Option[vpr.DomainAxiom] =
    guardTriggerFunction(guard, region) map { function =>
      val formalArgs = function.formalArgs.toVector
      val actualArgs = formalArgs.map(_.localVar)

      val application = guardTriggerFunctionApplication(guard, actualArgs, region).get

      val trigger = vpr.Trigger(Vector(application))()

      val body = vpr.Forall(
        formalArgs,
        Vector(trigger),
        application
      )()

      vpr.DomainAxiom(
        s"${application.funcname}_bottom",
        body
      )(domainName = regionStateTriggerFunctionsDomainName)
    }




  def guardPredicateName(guard: PGuardDecl, region: PRegion): String =
    s"${region.id.name}_${guard.id.name}"

  def extractGuardAndRegionNameFromGuardPredicateName(guardPredicateName: String)
  : (String, String) = {

    val splittedName = guardPredicateName.split("_")

    (splittedName(0), splittedName(1))
  }

  def extractGuardDeclAndRegion(guardExp: PRegionedGuardExp): (PGuardDecl, PRegion) = {
    semanticAnalyser.entity(guardExp.guard) match {
      case GuardEntity(guardDecl, region) => (guardDecl, region)
    }
  }

  def guardPredicate(guard: PGuardDecl, region: PRegion): vpr.Predicate = {
    guardPredicateCache.getOrElseUpdate(
      (guard, region),
      {
        val regionIdArgument = vpr.LocalVarDecl("$r", translate(PRegionIdType()))()
        val otherArguments = guard.formalArguments map translate

        (guard.modifier,otherArguments) match {
          case (_: PUniqueGuard | _: PDuplicableGuard, args) =>
            vpr.Predicate(
              name = guardPredicateName(guard, region),
              formalArgs = regionIdArgument +: args,
              body = None
            )()

          case (_: PDivisibleGuard, perm +: args) =>
            vpr.Predicate(
              name = guardPredicateName(guard, region),
              formalArgs = regionIdArgument +: args,
              body = None
            )()
        }
      }
    )
  }



  def translate(guardExp: PRegionedGuardExp): vpr.Exp = {

    val (guardDecl, region) = extractGuardDeclAndRegion(guardExp)

    val (guardPredicateAccess, guardPredicateAccessLoc) =
      translateUseOf(guardExp, guardDecl, region)

    errorBacktranslator.addReasonTransformer {
      case e: vprrea.InsufficientPermission if e causedBy guardPredicateAccessLoc =>
        InsufficientGuardPermissionError(guardExp)
    }

    guardPredicateAccess
  }

  def translateUseOf(guardExp: PRegionedGuardExp, guardDecl: PGuardDecl, region: PRegion)
  : (vpr.Exp, vpr.PredicateAccess) = {

    val vprGuardPredicate = guardPredicate(guardDecl, region)

    val translatedRegionId = translate(guardExp.regionId)

    /* acc(guard(r,args), perm) */
    def accessPredicate(args: Vector[vpr.Exp], perm: vpr.Exp): vpr.PredicateAccessPredicate =
      vpr.PredicateAccessPredicate(
        vpr.PredicateAccess(
          translatedRegionId +: args,
          vprGuardPredicate.name
        )().withSource(guardExp),
        perm
      )().withSource(guardExp)

    /* guardT(args) */
    def triggerPart(args: Vector[vpr.Exp]): vpr.Exp =
      guardTriggerFunctionApplication(
        guardDecl,
        translatedRegionId +: args,
        region
      ).get

    /* guardT(args) && body */
    def triggerWrapper(args: Vector[vpr.Exp], body: vpr.Exp): vpr.Exp =
      vpr.And(
        triggerPart(args),
        body
      )()

    def wrapExp(args: Vector[vpr.Exp], exp: vpr.Exp): vpr.Exp =
      if (USE_GUARD_SETS && args.nonEmpty) {
        triggerWrapper(args, exp)
      } else {
        exp
      }

    guardExp.argument match {
      case PStandartGuardArg(args) =>
        constructFromModifier(
          guardDecl.modifier,
          args map translate
        ){ case (predArgs, perm) =>
          val body = accessPredicate(predArgs, perm)

          (wrapExp(predArgs, body), body.loc)
        }

      case PSetGuardArg(set) =>
        val (conditional, decls) = extractGuardSetArgConditional(set, guardDecl)

        constructFromModifier(
          guardDecl.modifier,
          decls map (_.localVar)
        ){ case (predArgs, perm) =>
          val body = accessPredicate(predArgs, perm)

          /* {G_T(as)}{as in G_set} */
          val triggers = Vector(
            vpr.Trigger(
              Vector(
                guardTriggerFunctionApplication(
                  guardDecl,
                  translatedRegionId +: predArgs,
                  region
                ).get
              )
            )(),
            vpr.Trigger(
              Vector(
                conditional
              )
            )()
          )

          /* \/as. as in G_set ==> G_T(as) */
          val triggerExtra = if (USE_GUARD_SETS) {
            vpr.Forall(
              decls,
              triggers,
              vpr.Implies(
                conditional,
                triggerPart(predArgs)
              )()
            )()
          } else {
            vpr.TrueLit()()
          }

          /* \/as :: {G_T(as)}{as in G_set} as in G_set ==> G_T(as) && acc(G(r,as), perm) */
          val total = vpr.And(
            triggerExtra,
            vpr.Forall(
              decls,
              triggers,
              vpr.Implies(
                conditional,
                body
              )()
            )()
          )()

          (total, body.loc)
        }
    }
  }

  def regionStateChangeAllowedByGuard(region: PRegion,
                                      vprRegionInArgs: Vector[vpr.Exp],
                                      usedGuards: Vector[PRegionedGuardExp],
                                      vprFrom: vpr.Exp,
                                      vprTo: vpr.Exp,
                                      guardArgEvaluationLabel: vpr.Label)
  : vpr.Assert = {

    def guardArgEval(arg: vpr.Exp): vpr.Exp =
      vpr.LabelledOld(arg, guardArgEvaluationLabel.name)()

    /* from == to */
    val vprUnchanged = vpr.EqCmp(vprFrom, vprTo)()

    // FIXME: Assumes, every guard kind only occurs once (in guards and action). Maybe automatically combine all guards of the same kind
    val usedGuardsMap = usedGuards.map(g => g.guard.name -> g.argument).toMap

    def isRelevantAction(action: PAction): Boolean = {
      // FIXME: assumes globally unique guard name
      val actionKinds = action.guards map (_.guard.name)

      actionKinds forall usedGuardsMap.contains
    }

    val relevantActions = region.actions filter isRelevantAction

    val vprActionConstraints: Vector[vpr.Exp] =
      relevantActions.map(action => {

        val vprExistentialConstraint = stateConstraintsFromAction(
          action,
          vprFrom,
          vprTo,
          vpr.TrueLit()())

        val constraints: Vector[vpr.Exp] = action.guards map { case PBaseGuardExp(actionGuardId, actionGuardArg) =>

          val actionGuardKind = semanticAnalyser.entity(actionGuardId) match {
            case GuardEntity(guardDecl, `region`) => guardDecl
          }

          val relevantUsedGuardArg = usedGuardsMap(actionGuardId.name)

          (relevantUsedGuardArg, actionGuardArg) match {

            case (PStandartGuardArg(heldGuardArgs), PStandartGuardArg(requiredGuardArgs)) =>
              (actionGuardKind.modifier, heldGuardArgs, requiredGuardArgs) match {

                case (_: PUniqueGuard | _: PDuplicableGuard, haveArgs, sollArgs) =>
                  /* used_guard_args == action_guard_args */
                  viper.silicon.utils.ast.BigAnd(
                    haveArgs.zip(sollArgs).map{ case (h,s) =>
                      vpr.EqCmp(guardArgEval(translate(h)), translate(s))()
                    }
                  )

                case (_: PDivisibleGuard, r +: heldPerm +: haveArgs, requiredPerm +: sollArgs) =>
                  /* perm_required <= perm_held && used_guard_args == action_guard_args */
                  viper.silicon.utils.ast.BigAnd(
                    vpr.PermLeCmp(translate(requiredPerm), translate(heldPerm))() +:
                    haveArgs.zip(sollArgs).map{ case (h,s) =>
                      vpr.EqCmp(guardArgEval(translate(h)), translate(s))()
                    }
                  )
              }

            case (PStandartGuardArg(heldGuardArgs), PSetGuardArg(requiredGuardSet)) =>
              (actionGuardKind.modifier, heldGuardArgs) match {

                case (_: PUniqueGuard | _: PDuplicableGuard, haveArgs) =>
                  /* action_guard_set subset {tuple(used_guard_args)} */
                  val guardElem = tupleWrap(haveArgs map translate)

                  vpr.AnySetSubset(
                    translate(requiredGuardSet),
                    guardArgEval(vpr.ExplicitSet(Seq(guardElem))())
                  )()
              }

            case (PSetGuardArg(heldGuardSet), PStandartGuardArg(requiredGuardArgs)) =>
              (actionGuardKind.modifier, requiredGuardArgs) match {

                case (_: PUniqueGuard | _: PDuplicableGuard, sollArgs) =>
                  /* tuple(action_guard_args) in used_guard_set */
                  val sollArgsTuple = tupleWrap(sollArgs map translate)

                  vpr.AnySetContains(
                    sollArgsTuple,
                    guardArgEval(translate(heldGuardSet))
                  )()
              }

            case (PSetGuardArg(heldGuardSet), PSetGuardArg(actionGuardSet)) =>

              val (actionGuardconditional, actionGuardDecls) =
                extractGuardSetArgConditional(actionGuardSet, actionGuardKind)

              actionGuardKind.modifier match {

                case _: PUniqueGuard | _: PDuplicableGuard =>
                  /* \/xs :: tuple(xs) in action_guard_set ==>  tuple(xs) in used_guard_set */
                  val actionGuardElem = tupleWrap(actionGuardDecls map (_.localVar))

                  vpr.Forall(
                    actionGuardDecls,
                    Vector.empty,
                    vpr.Implies(
                      actionGuardconditional,
                      vpr.AnySetContains(
                        actionGuardElem,
                        translate(heldGuardSet)
                      )()
                    )()
                  )()
              }
          }
        }

        val binderInstantiations: Map[String, vpr.Exp] =
          action.binders.map(binder =>
            if (AstUtils.isBoundVariable(action.from, binder)) {
              binder.id.name -> vprFrom
            } else if (AstUtils.isBoundVariable(action.to, binder)) {
              binder.id.name -> vprTo
            } else {
              val guardOption = action.guards find { _.argument match {
                case PStandartGuardArg(args) =>
                  args.exists(AstUtils.isBoundVariable(_, binder))

                case _ => false
              }}

              guardOption match {
                case Some(PBaseGuardExp(guardId, PStandartGuardArg(guardArguments))) =>
                  /* The bound variable is a direct argument of the action guard G, i.e. the action
                   * guard is of the shape G(..., k, ...).
                   */

                  val argumentIndex = /* Index of k in G(..., k, ...) */
                    guardArguments.indexWhere(arg => AstUtils.isBoundVariable(arg, binder))

                  usedGuardsMap(guardId.name) match {
                    case PStandartGuardArg(args) =>
                      val vprArgument = /* Guard predicate is G(r, ..., k, ...) */
                        translate(args(argumentIndex))

                      binder.id.name -> vprArgument

                    case _ =>
                      sys.error(
                        s"The action at ${action.lineColumnPosition} does not belong to the class of "+
                          "currently supported actions. See issue #51 for further details.")
                  }

                case _ =>
                  sys.error(
                    s"The action at ${action.lineColumnPosition} does not belong to the class of "+
                      "currently supported actions. See issue #51 for further details.")
              }
            }
          )(breakOut)

        val substitutes: Map[vpr.LocalVar, vpr.Exp] =
          vprExistentialConstraint.variables.map(v =>
            v.localVar -> binderInstantiations(v.name)
          )(breakOut)

        val body = vpr.And(
          vprExistentialConstraint.exp,
          viper.silicon.utils.ast.BigAnd(constraints)
        )()

        body.replace(substitutes)
      })

    val vprConstraint = viper.silicon.utils.ast.BigOr(vprUnchanged +: vprActionConstraints)

    vpr.Assert(
      /* The AST simplifier is invoked because the substitution of the bound action variables
       * will result in several trivially-true subexpressions of the shape
       * state(r, x) == state(r, x).
       */
      viper.silver.ast.utility.Simplifier.simplify(vprConstraint)
    )()
  }

  def stateConstraintsFromAction(action: PAction,
                                 vprFrom: vpr.Exp,
                                 vprTo: vpr.Exp,
                                 vprGuardCheck: vpr.Exp)
  : vpr.Exists = {

    /* Let action be defined as follows:
     *   ?xs | c(xs) | G(g(xs)): e(xs) ~> e'(xs)
     */

    /* e(xs) == from */
    val vprFromWasPreHavocState =
      vpr.EqCmp(
        translate(action.from),
        vprFrom
      )()

    /* e'(xs) == to */
    val vprToIsNewState =
      vpr.EqCmp(
        translate(action.to),
        vprTo
      )()

    /* c(xs) */
    val vprCondition = translate(action.condition)

    /*  e(xs) == from ∧ e'(xs) == to ∧ c(x) ∧ guard_check */
    val vprExistentialBody =
      viper.silicon.utils.ast.BigAnd(
        Vector(
          vprFromWasPreHavocState,
          vprToIsNewState,
          vprCondition,
          vprGuardCheck))

    /* ∃ xs · body(xs) */
    vpr.Exists(
      action.binders map localVariableDeclaration,
      vprExistentialBody
    )()
  }

  def assembleCheckIfEnvironmentMayHoldActionGuard(region: PRegion,
                                                   vprRegionId: vpr.Exp,
                                                   action: PAction)
  : vpr.Exp = viper.silicon.utils.ast.BigAnd(
    action.guards.map{case PBaseGuardExp(gid, gargs) =>
      assembleCheckIfEnvironmentMayHoldBaseActionGuard(region, vprRegionId, gid, gargs)
    }
  )

  private def assembleCheckIfEnvironmentMayHoldBaseActionGuard(region: PRegion,
                                                               vprRegionId: vpr.Exp,
                                                               guardId: PIdnUse,
                                                               guardArgument: PGuardArg)
  : vpr.Exp = semanticAnalyser.entity(guardId) match {
    case GuardEntity(guardDecl, `region`) =>

      /* acc(G(r,args), perm) */
      def currentPerm(args: Vector[vpr.Exp]): vpr.CurrentPerm =
        vpr.CurrentPerm(
          vpr.PredicateAccess(
            vprRegionId +: args,
            guardPredicate(guardDecl, region).name
          )()
        )()

      guardArgument match {
        case PStandartGuardArg(guardArguments) =>

          (guardDecl.modifier, guardArguments) match {
            case (_: PDuplicableGuard, args) =>
              /* true */
              vpr.TrueLit () ()

            case (_: PUniqueGuard, args) =>
              /* perm(G(r,args)) == none */
              vpr.EqCmp(currentPerm(args map translate), vpr.NoPerm ()())()

            case (_: PDivisibleGuard, requiredPerm +: args) =>
              /* perm(G(r,args)) <= 1 - perm_required */
              vpr.PermLeCmp(
                currentPerm(args map translate),
                vpr.PermSub(
                  vpr.FullPerm()(),
                  translate(requiredPerm)
                )()
              )()
          }

        case PSetGuardArg(set) =>
          val (conditional, decls) = extractGuardSetArgConditional(set, guardDecl)

          (guardDecl.modifier, decls map (_.localVar)) match {

            case (_: PDuplicableGuard, _) =>
              /* true */
              vpr.TrueLit()()

            case (_: PUniqueGuard, translatedArgs) =>
              /* perm(G(r,xs)) == none */
              val body = vpr.EqCmp(currentPerm(translatedArgs), vpr.NoPerm()())()

              /* {G_T(r,xs)}{tuple(xs) in G_set} */
              val triggers = Vector(
                vpr.Trigger(
                  Vector(
                    guardTriggerFunctionApplication(
                      guardDecl,
                      vprRegionId +: translatedArgs,
                      region
                    ).get
                  )
                )(),
                vpr.Trigger(
                  Vector(
                    conditional
                  )
                )()
              )

              /* forall xs :: {G_T(r,xs)}{tuple(xs) in G_set} tuple(xs) in set ==> perm(guard(r,xs)) = none */
              vpr.Forall(
                decls,
                triggers,
                vpr.Implies(
                  conditional,
                  body
                )()
              )()
          }
      }

    case _ =>
      sys.error(
        s"Unexpectedly failed to find a declaration for the guard denoted by " +
          s"${guardId} (${guardId.position})")
  }

  private def tupleWrap(args: Vector[vpr.Exp]): vpr.Exp =
    vpr.DomainFuncApp(
      func = preamble.tuples.tuple(args.length),
      args = args,
      typVarMap = preamble.tuples.typeVarMap(args map (_.typ))
    )()

  private def extractGuardSetArgConditional(set: PExpression, guardDecl: PGuardDecl): (vpr.Exp, Vector[vpr.LocalVarDecl]) = {

    val expectedNumOfArguments = guardDecl.formalArguments.length

    semanticAnalyser.typ(set) match {

      case PSetType(elementType) if expectedNumOfArguments == 1 =>
        val vipElemTypes = translate(elementType)
        val decl = vpr.LocalVarDecl(s"$$a", vipElemTypes)()

        /* a in set */
        val conditional = vpr.AnySetContains(
          decl.localVar,
          translate(set)
        )()

        (conditional, Vector(decl))

      case PSetType(PTupleType(elementTypes)) if expectedNumOfArguments > 1 =>
        val vipElemTypes = elementTypes map translate

        val decls = vipElemTypes.zipWithIndex map { case (typ, ix) =>
          vpr.LocalVarDecl(s"$$a_$ix", typ)()
        }

        /* tuple(a1,..,an) in set */
        val conditional = vpr.AnySetContains(
          vpr.DomainFuncApp(
            func = preamble.tuples.tuple(decls.length),
            args = decls map (_.localVar),
            typVarMap = preamble.tuples.typeVarMap(vipElemTypes)
          )(),
          translate(set)
        )()

        (conditional, decls)

      case other =>
        sys.error(s"${set.pretty} should be of type Tuple but is ${other}")
    }
  }

  private def constructFromModifier[A](modifier: PModifier,
                                       expArgs: Vector[vpr.Exp],
                                       dfltPerm: vpr.Exp = vpr.FullPerm()())
                                      (constructor: (Vector[vpr.Exp], vpr.Exp) => A): A = {

    (modifier, expArgs) match {
      case (_: PUniqueGuard | _:PDuplicableGuard, args) =>
        constructor(args, dfltPerm)

      case (_: PDivisibleGuard, perm +: args) =>
        constructor(args, perm)
    }
  }

}
