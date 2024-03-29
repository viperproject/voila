/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import scala.collection.immutable.ListSet
import scala.language.implicitConversions
import org.bitbucket.inkytonik.kiama.==>
import org.bitbucket.inkytonik.kiama.attribution.{Attribution, Decorators}
import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.{id => _, _}
import org.bitbucket.inkytonik.kiama.util.Messaging._
import viper.voila.VoilaGlobalState
import viper.voila.reporting.PIdnNodeIdentifier

class SemanticAnalyser(tree: VoilaTree) extends Attribution {
  val symbolTable = new SymbolTable()
  import symbolTable._

  val decorators = new Decorators(tree)
  import decorators._

  lazy val errors: Messages =
    collectMessages(tree) {
      case decl: PIdnDef if entity(decl) == MultipleEntity() =>
        error(decl, s"${decl.name} is declared more than once")

      case use: PIdnUse =>
        use match {
          case tree.parent(PLocation(receiver, field)) if use eq field =>
            check(typeOfIdn(receiver.id)) {
              case PRefType(referencedTyp) =>
                check(entity(referencedTyp)) {
                  case StructEntity(struct) =>
                    error(
                      receiver,
                      s"Receiver $receiver does not have a field $field",
                      !struct.fields.exists(_.id.name == field.name))

                  case other if other.isError =>
                    error(receiver, s"Receiver $receiver is not of struct type")
                }

              case PRegionIdType() =>
                val region = usedWithRegion(receiver.id)

                 error(
                   receiver,
                   s"Receiver $receiver does not have a field $field",
                   !region.fields.exists(_.id.name == field.name))

              case other if !other.isInstanceOf[PUnknownType] =>
                error(receiver, s"Receiver $receiver is not of reference type")
            }

          case _ =>
            error(use, s"${use.name} is not declared", entity(use) == UnknownEntity())
        }

      case exp: PExpression if typ(exp) == PUnknownType() =>
        error(exp, s"$exp could not be typed")

      case predicateDecl @ PPredicate(predicate, _, body) =>
        val collectRegionPredicateExpressions =
          collect[Vector, PPredicateExp] {
            case exp: PPredicateExp if entity(exp.predicate).isInstanceOf[RegionEntity] => exp
          }

        val regionPredicateExpressions = collectRegionPredicateExpressions(body)

        error(
          predicateDecl,
          s"Regular predicates may currently not contain region predicates, but predicate " +
              s"${predicate.name} contains the following: " +
              s"${regionPredicateExpressions.map(_.predicate.name).mkString(", ")}",
          regionPredicateExpressions.nonEmpty)

      case PProcedure(_, _, _, _, _, pres, posts, _, optBody, atom, _) =>
        val contractMessages =
          (pres.map(_.assertion) ++ posts.map(_.assertion))
              .flatMap(exp => reportTypeMismatch(exp, PBoolType()))

        val atomicityMessages =
          optBody match {
            case Some(body) =>
              error(
                body,
                "Unexpectedly found a non-atomic and non-ghost statement " +
                    s"(${body.statementName}) in an atomic context",
                (atom == PAbstractAtomic() || atom == PPrimitiveAtomic()) &&
                    atomicity(body) == AtomicityKind.Nonatomic)
            case None =>
              Vector.empty
          }

        contractMessages ++ atomicityMessages

      case region: PRegion =>
        if (region.formalInArgs.length < 2) {
          error(
            region,
            s"Region ${region.id.name} must have at least two parameters: id and level")
        } else {
          val Vector(firstParam, secondParam) = region.formalInArgs.take(2)

          val idTypeMessage =
            error(
              firstParam,
              s"Region ${region.id.name}'s first parameter must be of type ${PRegionIdType().pretty}, " +
                  s"but got: ${firstParam.typ.pretty}",
              firstParam.typ != PRegionIdType())

          val levelTypeMessage =
            error(
              secondParam,
              s"Region ${region.id.name}'s second parameter must be of type ${PIntType().pretty}, " +
                  s"but got: ${secondParam.typ.pretty}",
              secondParam.typ != PIntType())

          idTypeMessage ++ levelTypeMessage
        }

      case action: PAction => // TODO: add guard type check and it seems that condition type check is missing
        val typeMessages =
          reportTypeMismatch(action.to, typ(action.from)) ++
              reportTypeMismatch(action.condition, PBoolType())

        val freeVariableMessages = {
          val freeVars = (
            freeVariables(action.condition) ++
                freeVariables(action.from) ++
                freeVariables(action.to) ++
                (action.guards flatMap freeVariables)
            ).filterNot(fv => action.binders.exists(_.id.name == fv.name))

          error(
            action,
            s"Actions may not contain free variables, but found: ${freeVars.mkString(", ")}",
            freeVars.nonEmpty)
        }

        val guardMessages =
          action.guards.flatMap { case guardExp @ PBaseGuardExp(guardId, guardArgument) =>
            checkUse(entity(guardId)) {
              case GuardEntity(decl, declaringRegion) =>
                val regionMessages =
                  error(
                    guardExp,
                    s"Guard ${guardId.name} is not a guard of this region",
                    !enclosingMember(action).contains(declaringRegion))

                val typeMessages =
                  check(guardArgument) {
                    case PStandardGuardArg(guardArguments) => check(decl.modifier) {
                      case _: PUniqueGuard | _: PDuplicableGuard =>
                        val lengthMessages =
                          reportArgumentLengthMismatch(guardId, decl.id, decl.formalArguments.length, guardArguments.length)

                        val typeMessages =
                          if (lengthMessages.isEmpty) {
                            reportTypeMismatch(guardArguments, decl.formalArguments)
                          } else {
                            Vector.empty
                          }

                        lengthMessages ++ typeMessages

                      case _: PDivisibleGuard =>
                        // FIXME: Indexed divisible guards are currently not supported, add message
                        val lengthMessages =
                          reportArgumentLengthMismatch(guardId, decl.id, 1 /* decl.formalArguments.length */, guardArguments.length)

                        val typeMessages =
                          if (lengthMessages.isEmpty) {
                            reportTypeMismatch(guardArguments.head, PFracType(), typ(guardArguments.head)) ++
                            reportTypeMismatch(guardArguments.tail, decl.formalArguments.tail)
                          } else {
                            Vector.empty
                          }

                        lengthMessages ++ typeMessages
                    }

                    case PSetGuardArg(guardSet) => check(decl.modifier) {
                      case _: PUniqueGuard | _: PDuplicableGuard =>

                        reportTypeMismatch(guardSet, expectedGuardSetTyp(decl), typ(guardSet))

                      case _: PDivisibleGuard =>
                        error(guardId, s"Indexed divisible guards are currently not supported, but got ${guardId.name}")
                    }
                  }

                regionMessages ++ typeMessages

              case _ =>
                error(guardId, s"Expected a guard, but got ${guardId.name}")
            }
          }

        typeMessages ++ freeVariableMessages ++ guardMessages

      case PAssign(lhs, rhs) =>
        val lhsEntity = entity(lhs)

        error(
          lhs,
          s"Cannot assign to ${lhs.name}",
          !lhsEntity.isInstanceOf[LocalVariableLikeEntity]
        ) ++ reportTypeMismatch(rhs, typeOfIdn(lhs), typ(rhs))

      case PHeapRead(localVariable, location) =>
        check(entity(localVariable)) {
          case localVariableEntity: LocalVariableLikeEntity =>
            reportTypeMismatch(location, localVariableEntity.typ, typeOfLocation(location))

          case other =>
            checkUse(other){ case _ =>
              error(
                localVariable,
                "Type error: expected a local variable, but found " +
                  PIdnNodeIdentifier.fullyQualified(localVariable, other))
            }
        }

      case PHeapWrite(location, rhs) =>
        reportTypeMismatch(location, typeOfLocation(location), typ(rhs))

      case newStmt @ PNewStmt(lhs, constructor, arguments, optGuards, optInitializer) =>
        val lhsEntity = entity(lhs)

        val lhsMessages =
          error(
            lhs,
            s"Cannot assign to ${lhs.name}",
            !lhsEntity.isInstanceOf[LocalVariableLikeEntity])

        val constructorMessages =
          entity(constructor) match {
            case StructEntity(structDecl) => /* s := new struct(e1,  ...) */
              val typeMessages =
                reportTypeMismatch(lhs, typeOfIdn(constructor), typeOfIdn(lhs))

              val argumentsMessages =
                if (arguments.size > structDecl.fields.size) {
                  error(
                    newStmt,
                    s"Wrong number of arguments for struct constructor '${constructor.name}', got ${arguments.size} "
                      + s"but expected at most ${structDecl.fields.size}")
                } else {
                  reportTypeMismatch(arguments, structDecl.fields.take(arguments.size))
                }

              val guardsMessages =
                optGuards.fold(noMessages)(
                  error(_, s"Struct constructor does not take a list of guards"))

              val initializerMessages =
                optInitializer.fold(noMessages)(
                  error(_, s"Struct constructor does not take an initializer block"))

              typeMessages ++ argumentsMessages ++ guardsMessages ++ initializerMessages

            case RegionEntity(regionDecl) => /* r := new Region(lvl, e1, ...) with G1 && ... { init }*/
              val typeMessages =
                reportTypeMismatch(lhs, PRegionIdType(), typeOfIdn(lhs))

              val argumentsMessages =
                if (arguments.size != regionDecl.formalInArgs.size - 1) {
                  val hint =
                    if (arguments.size > regionDecl.formalInArgs.size - 1) " (note that the region id must be omitted)"
                    else ""

                  error(
                    newStmt,
                    s"Wrong number of arguments for region constructor '${constructor.name}', got ${arguments.size} "
                      + s"but expected ${regionDecl.formalInArgs.size - 1}"
                      + hint)
                } else {
                  reportTypeMismatch(arguments, regionDecl.formalInArgs.tail)
                }

              val guardsMessages =
                optGuards.fold(noMessages)(_.flatMap(guardExp =>
                  entity(guardExp.guard) match {
                    case GuardEntity(_, `regionDecl`) =>
                      noMessages
                    case _ =>
                      error(
                        guardExp,
                        s"Region ${constructor.name} does not declare guard ${guardExp.guard.name}")
                  }
                ))

              typeMessages ++ argumentsMessages ++ guardsMessages

            case _ =>
              error(constructor, s"Cannot instantiate ${constructor.name}, struct or region expected")
          }

        lhsMessages ++ constructorMessages

      case call: PProcedureCall =>
        checkUse(entity(call.procedure)) {
          case ProcedureEntity(decl) => (
               reportArgumentLengthMismatch(call, decl.id, decl.formalArgs.length, call.arguments.length)
            ++ reportArgumentLengthMismatch(call, decl.id, decl.formalReturns.length, call.rhs.length)
            ++ reportTypeMismatch(call.arguments, decl.formalArgs)
            ++ call.rhs.zip(decl.formalReturns).flatMap { case (rhs, formal) => reportTypeMismatch(rhs, formal.typ) }
            ++ { call match {
                   case tree.parent(_: PLemmaApplication) =>
                     error(call, "only lemma methods are invoked with 'use'", !decl.lemma.flag)
                   case _ =>
                     error(call, "lemma methods can only be invoked with 'use'", decl.lemma.flag)
               }}
            )
//            ++ reportTypeMismatch(call.rhs, decl.formalReturns)) /* TODO: See comment for reportTypeMismatch */

          case _ =>
            error(call.procedure, s"Cannot call ${call.procedure}")
        }

      case fork: PFork =>
        error(fork.call, s"expected non-atomic call, but got ${fork.call}", atomicity(fork.call) != AtomicityKind.Nonatomic)

      case parallelCall: PParallelCall =>
        parallelCall.calls.flatMap { call =>
          error(call, s"expected non-atomic call, but got $call", atomicity(call) != AtomicityKind.Nonatomic)
        }

      case acquireGuard: PAcquireDuplicableGuard =>
        val guardMod = entity(acquireGuard.guard.guard).asInstanceOf[GuardEntity].declaration.modifier
        error(acquireGuard, "only duplicable guards can be used in an acquire statement", !guardMod.isInstanceOf[PDuplicableGuard])

      case _rule @ (_: POpenRegion | _: PUpdateRegion) =>
        val rule = _rule.asInstanceOf[PRuleStatement]

        reportAtomicityMismatch(
          rule.body,
          AtomicityKind.Atomic,
          s"The body of a ${rule.statementName} block must be atomic")

      case useAtomic: PUseAtomic =>
        val atomicityMessages =
          reportAtomicityMismatch(
            useAtomic.body,
            AtomicityKind.Atomic,
            s"The body of a ${useAtomic.statementName} block must be atomic")

        val idMessages =
          reportUsingWithIDMismatch(useAtomic, useAtomic.regionPredicate, useAtomic.guards)

        atomicityMessages ++ idMessages

      case makeAtomic: PMakeAtomic =>
        reportUsingWithIDMismatch(makeAtomic, makeAtomic.regionPredicate, makeAtomic.guards)

      case fold: PFold => reportAbstractPredicateUnFoldIng(fold)
      case unfold: PUnfold => reportAbstractPredicateUnFoldIng(unfold)

      case exp: PExpression => (
           reportTypeMismatch(exp, expectedType(exp), typ(exp))
        ++ check(exp) {
              case PIdnExp(id) =>
                checkUse(entity(id)) {
                  case _: ProcedureEntity =>
                    error(id, "Cannot refer to procedures directly")
                }

              case PPredicateExp(id, args) =>
                checkUse(entity(id)) {
                  case PredicateEntity(decl) =>
                    (   reportArgumentLengthMismatch(exp, decl.id, decl.formalArgs.length, args.length)
                     ++ reportTypeMismatch(args, decl.formalArgs))

                  case RegionEntity(decl) =>
                    /* A region predicate has the following argument structure:
                     * one region id, followed by multiple in-arguments, optionally followed by
                     * out-arguments.
-                    */
                    val expectedArgCounts =
                      (decl.formalInArgs.length,
                       decl.formalInArgs.length + decl.formalOutArgs.length + 1)

                    val actualArgCount = args.length

                    val lengthMessages =
                      error(
                        id,
                          s"Wrong number of arguments for '${id.name}': expected at least "
                        + s"${expectedArgCounts._1} (no out-arguments) and at most "
                        + s"${expectedArgCounts._2} (all out-arguments), but got $actualArgCount",
                        !(expectedArgCounts._1 <= actualArgCount && actualArgCount <= expectedArgCounts._2))

                    val expectedArgumentTypes =
                      decl.formalInArgs.map(_.typ) ++
                      decl.formalOutArgs.map(_.typ) :+
                      typ(decl.state)

                    val typeMessages =
                      args.zip(expectedArgumentTypes).flatMap { case (arg, tip) => reportTypeMismatch(arg, tip) }

                    lengthMessages ++ typeMessages

                  case _ =>
                    error(id, s"Expected a predicate or a region, but got ${id.name}")
                }

              case PRegionedGuardExp(guardId, regionId, argument) =>
                checkUse(entity(guardId)) {
                  case GuardEntity(decl, _) =>
                    argument match {
                      case PStandardGuardArg(arguments) =>
                        val lengthMessages =
                          reportArgumentLengthMismatch (exp, decl.id, decl.formalArguments.length, arguments.length)

                        val typeMessages =
                          if (lengthMessages.isEmpty) {
                            reportTypeMismatch (arguments, decl.formalArguments) ++
                            reportTypeMismatch (regionId, PRegionIdType (), typ (regionId) )
                          } else {
                            Vector.empty
                          }

                        lengthMessages ++ typeMessages

                      case PSetGuardArg(setArg) =>
                        reportTypeMismatch(setArg, expectedGuardSetTyp(decl), typ(setArg))
                    }

                  case _ =>
                    error(guardId, s"Expected a guard, but got ${guardId.name}")
                }

              case PTupleGet(tuple, index) =>
                check(typ(tuple)) {
                  case PTupleType(elementTypes) =>
                    error(exp, s"Out of bounds access in ${exp.pretty}", index >= elementTypes.length)
                }

              case unfolding: PUnfolding => reportAbstractPredicateUnFoldIng(unfolding)
          })
    }

  private def expectedGuardSetTyp(decl: PGuardDecl): PType =
    if(decl.formalArguments.length == 1) {
      PSetType(decl.formalArguments.head.typ)
    } else {
      PSetType(PTupleType(decl.formalArguments map (_.typ)))
    }

  private def reportArgumentLengthMismatch(offendingNode: PAstNode,
                                           callee: PIdnNode,
                                           formalArgCount: Int,
                                           actualArgCount: Int) = {

    error(
      offendingNode,
        s"Wrong number of arguments for '${callee.name}', got $actualArgCount "
      + s"but expected $formalArgCount",
      formalArgCount != actualArgCount)
  }

  private def reportTypeMismatch(actuals: Vector[PExpression], formals: Vector[PTypedDeclaration]): Messages =
    actuals zip formals flatMap { case (actual, formal) => reportTypeMismatch(actual, formal.typ) }

  /* TODO: Cannot also declare this method, due to type erase.
   *       It would not be necessary if PIdnUse replaced PIdnExp everywhere.
   */
  //  private def reportTypeMismatch(actuals: Vector[PIdnUse], formals: Vector[PTypedDeclaration]): Messages =
  //    actuals zip formals flatMap { case (actual, formal) => reportTypeMismatch(actual, formal.typ) }

  private def reportTypeMismatch(offendingNode: PExpression, expectedType: PType): Messages =
    reportTypeMismatch(offendingNode, Set(expectedType), typ(offendingNode))

  private def reportTypeMismatch(offendingNode: PIdnUse, expectedType: PType): Messages =
    reportTypeMismatch(offendingNode, Set(expectedType), typeOfIdn(offendingNode))

  private def reportTypeMismatch(offendingNode: PAstNode, expectedType: PType, foundType: PType)
                                : Messages = {

    reportTypeMismatch(offendingNode, Set(expectedType), foundType)
  }

  private def reportTypeMismatch(offendingNode: PAstNode,
                                 expectedTypes: Set[PType],
                                 foundType: PType)
                                : Messages = {

    assert(expectedTypes.nonEmpty)

    val text =
      if (expectedTypes.size == 1) {
        s"Type error: expected ${expectedTypes.head} but got $foundType"
      } else {
        s"Type error: expected one of ${expectedTypes.tail.mkString(", ")} or " +
        s"${expectedTypes.last}, but got $foundType"
      }

    error(offendingNode, text, !expectedTypes.exists(isCompatible(foundType, _)))
  }

  def reportAbstractPredicateUnFoldIng(foldUnfold: PFoldUnfold): Messages = {
    checkUse(entity(foldUnfold.predicateExp.predicate)) {
      case PredicateEntity(predicate) if predicate.body.isEmpty =>
        error(
          foldUnfold,
          s"Cannot (un)fold ${foldUnfold.predicateExp.pretty} because predicate ${predicate.id.name} is abstract")
    }
  }

  def reportAtomicityMismatch(stmt: PStatement, expectedAtomicity: AtomicityKind, text: String): Messages = {
    checkWith(atomicity(stmt))(atomicityKind =>
      error(
        stmt,
        text,
        atomicityKind != expectedAtomicity))
  }

  def reportUsingWithIDMismatch(offendingNode: PRuleStatement,
                                regionPredicate: PPredicateExp,
                                guards: Vector[PRegionedGuardExp])
                               : Messages = {

    val guardIds = guards.map(_.regionId).distinct

    if (guardIds.length > 1) {
      error(
        offendingNode,
        s"The guards used by ${offendingNode.statementName} must all be for the same region, " +
            s"but got different region IDs: ${guardIds.mkString(", ")}")
    } else {
      assert(guardIds.nonEmpty, "Expected at least one region ID, but got zero")

      error(
        offendingNode,
        s"Region and guard(s) used by ${offendingNode.statementName} don't share the same region ID: " +
            s"${regionPredicate.arguments.head} vs. ${guardIds.head}",
        regionPredicate.arguments.head != guardIds.head)
    }
  }

  /**
    * Are two types compatible?  If either of them are unknown then we
    * assume an error has already been raised elsewhere so we say they
    * are compatible with anything. Otherwise, the two types have to be
    * the same.
    */
  def isCompatible(t1: PType, t2: PType): Boolean = {
    (t1, t2) match {
      case (`t1`, `t1`) => true
      case (PRefType(id1), PRefType(id2)) => id1.name == id2.name
      case (_: PRefType, _: PNullType) | (_: PNullType, _: PRefType) => true
      case (_: PUnknownType, _) | (_, _: PUnknownType) => true
      case _ => false
    }
  }

  /**
    * The entity defined by a defining occurrence of an identifier.
    * Defined by the context of the occurrence.
    */
  lazy val definedEntity: PIdnDef => VoilaEntity =
    attr[PIdnDef, VoilaEntity] {
      case tree.parent(p) =>
        p match {
          case decl: PStruct=> StructEntity(decl)
          case decl: PProcedure => ProcedureEntity(decl)
          case decl: PPredicate => PredicateEntity(decl)
          case decl: PRegion => RegionEntity(decl)
          case tree.parent.pair(decl: PGuardDecl, region: PRegion) => GuardEntity(decl, region)
          case decl: PFormalArgumentDecl => FormalArgumentEntity(decl)
          case decl: PFormalReturnDecl => FormalReturnEntity(decl)
          case decl: PLocalVariableDecl => LocalVariableEntity(decl)
          case decl: PNamedBinder => LogicalVariableEntity(decl)
          case _ => UnknownEntity()
        }
    }

  /* TODO: The environment computation is a big mess!
   *       It has been adapted from a Kiama example
   *       (Kiama\library\src\test\scala\org\bitbucket\inkytonik\kiama\example\minijava\SemanticAnalyser.scala)
   *       but seemingly small differences in the AST design (Kiama has Class/Method and
   *       ClassBody/MethodBody, Voila doesn't) make a big difference in the environment
   *       computation.
   *       Ultimately, I don't really know how the environment computation code works ...
   */

  /**
    * The environment to use to lookup names at a node. Defined to be the
    * completed defining environment for the smallest enclosing scope.
    */
  lazy val env: PAstNode => Environment =
    attr[PAstNode, Environment] {
      // At a scope-introducing node, get the final value of the
      // defining environment, so that all of the definitions of
      // that scope are present.
      case tree.lastChild.pair(_: PScope, c) =>
        defenv(c)

      // Otherwise, ask our parent so we work out way up to the
      // nearest scope node ancestor (which represents the smallest
      // enclosing scope).
      case tree.parent(p) =>
        env(p)
    }

  /**
    * The environment containing bindings for things that are being
    * defined. Much of the power of this definition comes from the Kiama
    * `chain` method, which threads the attribute through the tree in a
    * depth-first left-to-right order. The `envin` and `envout` definitions
    * are used to (optionally) update attribute value as it proceeds through
    * the tree.
    */
  lazy val defenv : Chain[Environment] =
    chain(defenvin, defenvout)

  def defenvin(in: PAstNode => Environment): PAstNode ==> Environment = {
    case program: PProgram =>
      /* At the root, create a new environment with all top-level members and all guards.
       * The latter is for simplicity, but means that guard names must be globally unique.
       */

      val topLevelBindings = (
           program.regions.map(r => r.id.name -> RegionEntity(r))
        ++ program.structs.map(p => p.id.name -> StructEntity(p))
        ++ program.predicates.map(p => p.id.name -> PredicateEntity(p))
        ++ program.procedures.map(p => p.id.name -> ProcedureEntity(p)))

      val guardBindings =
        program.regions.flatMap(region =>
          region.guards.map(guard =>
            s"${guard.id.name}@${region.id.name}" -> GuardEntity(guard, region)))

      val bindings: Vector[(String, VoilaEntity)] = topLevelBindings ++ guardBindings

      bindings.foldLeft(rootenv()) { case (currentEnv, currentBinding) =>
        defineIfNew(currentEnv, currentBinding._1, MultipleEntity(), currentBinding._2)
      }

    case bindingContext: PBindingContext with PScope =>
      /* A binding context that defines its own scope, such as a set comprehension
       * Set(?c | 0 < c), results in adding a new scope (inside the outer environment)
       * that contains the bound variable.
       */
      var nextEnv = enter(in(bindingContext))

      def add(binder: PNamedBinder): Unit = {
        nextEnv = defineIfNew(nextEnv, binder.id.name, MultipleEntity(), definedEntity(binder.id))
      }

      bindingContext match {
        case action: PAction => action.binders foreach add
        case PSetComprehension(qvar, _, _) => add(qvar)
      }

      nextEnv

    case scope@(_: PScope) =>
      enter(in(scope))
  }

  def defenvout(out: PAstNode => Environment): PAstNode ==> Environment = {
     case scope@(_: PScope) =>
       leave(out(scope))

    case idef: PIdnDef =>
      idef match {
        case tree.parent(tree.parent(region: PRegion)) if region.formalOutArgs.exists(_.id eq idef) =>
          /* Region out args must be bound inside the interpretation; thus, don't add them here */
          out(idef)

        case tree.parent(tree.parent(_: PBindingContext with PScope)) | /* PAction, PSetComprehension */
             tree.parent(_: PScope) => /* PGuardDecl, PProcedure etc. */

          /* Don't add identifiers that have already been added (in defenvin) */
          out(idef)

        case _ =>
          defineIfNew(out(idef), idef.name, MultipleEntity(), definedEntity(idef))
      }
  }

  /**********************************************************
   *  TODO: Modify environment computation such that a PPredicateExp
   *          Region(a, ...)
   *        adds a binding from a to Region to the environment
   */

  /**
    * The program entity referred to by an identifier definition or use.
    */
  lazy val entity: PIdnNode => VoilaEntity =
    attr[PIdnNode, VoilaEntity] {
      case g @ tree.parent(PRegionedGuardExp(guardId, _, _)) if guardId eq g => lookupGuard(guardId)
      case g @ tree.parent(PBaseGuardExp(guard, _)) if guard eq g => lookupGuard(g)
      case n => lookup(env(n), n.name, UnknownEntity())
    }

  private def lookupGuard(guardId: PIdnNode): VoilaEntity = {
    /* Guards must currently be globally unique and we can therefore find the region it
     * belongs to simply by iterating over all regions.
     *
     * TODO: The current approach isn't ideal: guards must be globally unique, but are
     *       nevertheless suffixed in the environment by their region, which is why the
     *       region is also needed when looking up a guard.
     *       Either drop the requirement of globally-unique guards or don't suffix them
     *       with a region in the environment.
     */
    tree.root.regions.find(_.guards.exists(_.id.name == guardId.name)) match {
      case Some(region) =>
        lookup(env(guardId), s"${guardId.name}@${region.id.name}", UnknownEntity())
      case None =>
        UnknownEntity()
    }
  }

  lazy val usedWithRegion: PIdnNode => PRegion =
    attr[PIdnNode, PRegion](id => {
      val usages = regionIdUsedWith(id)
      assert(usages.nonEmpty)

      usages.head.region
    })

  /** Given a region identifier such as `r`, returns one of potentially many region assertions `Reg(r, ...)`. */
  lazy val usedWithRegionPredicate: PIdnNode => PPredicateExp =
    attr[PIdnNode, PPredicateExp](id => {
      val predicateUsages: Vector[RegionPredicateUsage] =
        regionIdUsedWith(id).collect { case rpg: RegionPredicateUsage => rpg }

      val predicateArguments =
        predicateUsages.map(_.arguments).distinct

      predicateArguments match {
        case Seq() =>
          sys.error(s"Could not associate region identifier $id with a region assertion (such as R($id, ...)).")
        case Seq(_) =>
          predicateUsages.head.source
        case _ =>
          sys.error(
            s"The in-arguments of a region assertion are not expected to change (in the scope " +
              s"of a single program member), but the following region assertions were found: " +
              s"${predicateUsages.map(_.source).mkString(", ")}. " +
              "Attention: for simplicity, semantically equivalent but syntactically different arguments " +
              "are currently rejected.")
      }
    })

  private lazy val regionIdUsedWith: PIdnNode => Vector[RegionIdUsage] =
    attr[PIdnNode, Vector[RegionIdUsage]](id => enclosingMember(id) match {
      case Some(member) =>
        var usages = Vector.empty[RegionIdUsage]

        everywhere(query[PAstNode] {
          case region: PRegion if region.regionId.id.name == id.name =>
            usages +:= RegionDeclarationUsage(id, region)

          case exp @ PPredicateExp(predicate, PIdnExp(`id`) +: _) =>
            entity(predicate) match {
              case RegionEntity(declaration) => usages +:= RegionPredicateUsage(id, declaration, exp)
              case _ => /* Do nothing */
            }

          case stmt: PNewStmt if stmt.lhs == id =>
            entity(stmt.constructor) match {
              case RegionEntity(declaration) => usages +:= NewStmtUsage(id, declaration, stmt)
              case _ => /* Do nothing */
            }
        })(member)

        val regions = usages.map(_.region).distinct

        if (regions.isEmpty) {
          sys.error(
            s"Could not associate region identifier $id with a region assertion. " +
              "This can, for example, happen if a guard is used (such as G@r), but the region " +
              "identifier (such as r) it is used with isn't used in a region assertion " +
              "(such as R(r, ...) or r := new R(...)). This is currently not supported.")
        } else if (regions.size > 1) {
          sys.error(
            s"Identifier $id is used as the region identifier of different region types: " +
              s"${regions.map(_.id.name).mkString(", ")}. This is not allowed.")
        } else {
          usages
        }

      case None =>
        sys.error(
          s"It appears that identifier $id is used as a region identifier, but in a scope/at a " +
            "program point where region identifiers are not expected.")
    })

  def enclosingMember(of: PAstNode): Option[PMember] =
    enclosingMemberAttr(of)(of)

  private lazy val enclosingMemberAttr: PAstNode => PAstNode => Option[PMember] =
    paramAttr[PAstNode, PAstNode, Option[PMember]] { of => {
      case member: PMember => Some(member)
      case tree.parent(p) => enclosingMemberAttr(of)(p)
    }}

  def enclosingMakeAtomic(of: PAstNode): PMakeAtomic =
    enclosingMakeAtomicAttr(of)(of)

  private lazy val enclosingMakeAtomicAttr: PAstNode => PAstNode => PMakeAtomic =
    paramAttr[PAstNode, PAstNode, PMakeAtomic] { of => {
      case makeAtomic: PMakeAtomic => makeAtomic
      case tree.parent(p) => enclosingMakeAtomicAttr(of)(p)
    }}

  def generalBindingContext(of: PNamedBinder): LogicalVariableContext =
    generalContextAttr(of.id)(of)

  def generalUsageContext(of: PIdnNode): LogicalVariableContext =
    generalContextAttr(of)(of)

  private lazy val generalContextAttr: PIdnNode => PAstNode => LogicalVariableContext =
    paramAttr[PIdnNode, PAstNode, LogicalVariableContext] { of => {
      case _: PInterferenceClause => LogicalVariableContext.Interference
      case _: PPreconditionClause => LogicalVariableContext.Precondition
      case _: PPostconditionClause => LogicalVariableContext.Postcondition
      case _: PInvariantClause => LogicalVariableContext.Invariant
      case _: PProcedure => LogicalVariableContext.Procedure
      case _: PRegion => LogicalVariableContext.Region
      case _: PPredicate => LogicalVariableContext.Predicate
      case tree.parent(p) => generalContextAttr(of)(p)
    }}

  def enclosingStatement(of: PAstNode): PStatement =
    enclosingStatementAttr(of)(of)

  private lazy val enclosingStatementAttr: PAstNode => PAstNode => PStatement =
    paramAttr[PAstNode, PAstNode, PStatement] { of => {
      case statement: PStatement => statement
      case tree.parent(p) => enclosingStatementAttr(of)(p)
    }}

  // TODO: Replace PAstNode with PExpression in enclosingAssertion and enclosingAssertionAttr.
  //       It is currently PAstNode because it is sometimes necessary to find the enclosing assertion of
  //       a PIdnUse. However, these should probably be PIdnExp anyway.
  def enclosingAssertion(of: PAstNode): PExpression =
    enclosingAssertionAttr(of)(of)

  private lazy val enclosingAssertionAttr: PAstNode => PAstNode => PExpression =
    paramAttr[PAstNode, PAstNode, PExpression] { of => {
      case tree.parent(p: PExpression) => enclosingAssertionAttr(of)(p)
      case p: PExpression => p
    }}

  def enclosingLoops(of: PAstNode): Vector[PWhile] =
    enclosingLoopsAttr(of, Vector.empty)(of)

  private lazy val enclosingLoopsAttr: ((PAstNode, Vector[PWhile])) => PAstNode => Vector[PWhile] =
    paramAttr[(PAstNode, Vector[PWhile]), PAstNode, Vector[PWhile]] { case (of, loops) => {
      case _: PMember => loops
      case tree.parent(p: PWhile) => enclosingLoopsAttr(of, loops :+ p)(p)
      case tree.parent(p) => enclosingLoopsAttr(of, loops)(p)
    }}

  lazy val isGhost: PStatement => Boolean =
    attr[PStatement, Boolean] {
      case _: PGhostStatement => true
      case heapAccess: PHeapAccess if typeOfIdn(heapAccess.location.receiver.id) == PRegionIdType() => true
      // TODO: The next cases currently prevent reaching the last case with isInNewRegionInitializerBlock.
      //       This might prevent correctly categorising statements inside initialiser blocks as ghost.
      case newStmt: PNewStmt => isNewRegionStatement(newStmt)
      case compound: PCompoundStatement => compound.components forall isGhost
      case stmt => isInNewRegionInitializerBlock(stmt)
    }

  lazy val isNewRegionStatement: PNewStmt => Boolean =
    attr[PNewStmt, Boolean](newStmt => {
      entity(newStmt.constructor) match {
        case _: StructEntity => false
        case _: RegionEntity => true
        case other => sys.error(s"Unexpectedly found $other")
      }
    })

  private lazy val enclosingNewStatementAttr: PStatement => PAstNode => Option[PNewStmt] =
    paramAttr[PStatement, PAstNode, Option[PNewStmt]] { of => {
      case newStmt: PNewStmt => Some(newStmt)
      case _: PMember => None
      case tree.parent(p) => enclosingNewStatementAttr(of)(p)
    }}

  def enclosingNewStatement(of: PStatement): Option[PNewStmt] =
    enclosingNewStatementAttr(of)(of)

  private lazy val isInNewRegionInitializerBlock: PStatement => Boolean =
    attr[PStatement, Boolean](stmt => {
      // NOTE: For simplicity, a statement s1 is currently considered to be inside the initialiser block of a
      // new-statement s2 iff s1 is a (transitive) child of s2. If new-statements could contain statements outside of
      // the initialiser block, the current check would no longer suffice.
      enclosingNewStatement(stmt) match {
        case None => false
        case Some(newStmt) => isNewRegionStatement(newStmt)
      }
    })

  /** Given an interference clause '?s in X on r', where the trailing 'on r' is optional,
    * interferenceOnRegionId returns the identifier 'r' of the region to which the interference
    * variable 's' belongs.
    * If 'on r' is provided, 'r' is returned.
    * Otherwise, the enclosing procedure's pre- and postconditions are searched for region
    * assertions 'R(r, ..., s)': if exactly one exists, 'r' is returned, otherwise an exception
    * is thrown.
    */
  lazy val interferenceOnRegionId: PInterferenceClause => PIdnUse =
    attr[PInterferenceClause, PIdnUse] {
      case PInterferenceClause(_, _, Some(regionId)) =>
        regionId
      case interferenceClause =>
        val stateVariableName = interferenceClause.variable.id.name
        val procedure = enclosingMember(interferenceClause).asInstanceOf[Option[PProcedure]].get

        var regionPredicateExpressions = Set.empty[PPredicateExp]

        everywhere(query[PPredicateExp] {
          case predicateExp: PPredicateExp => entity(predicateExp.predicate) match {
            case RegionEntity(region) =>
              if (predicateExp.arguments.length == region.explicitArgumentCount + 1) {
                predicateExp.arguments.last match {
                  case PIdnExp(PIdnUse(`stateVariableName`)) =>
                    regionPredicateExpressions = regionPredicateExpressions + predicateExp
                  case _ =>
                    /* Do nothing */
                }
              }
          }
        })(procedure.pres ++ procedure.posts)

        if (regionPredicateExpressions.isEmpty) {
          sys.error(
            s"Could not relate interference variable $stateVariableName to a region identifier. " +
                "Please add 'on r' (for the desired region identifier 'r') to the interference " +
                s"clause on line ${interferenceClause.lineColumnPosition}.")
        } else if (regionPredicateExpressions.size == 1) {
          regionPredicateExpressions.head.arguments.head.asInstanceOf[PIdnExp].id
        } else {
          val candidates = regionPredicateExpressions.map(_.arguments.head).mkString(",")

          sys.error(
            s"Could not uniquely relate interference variable $stateVariableName to a region " +
            s"identifier: found candidates $candidates. Please add 'on r' (for the desired region " +
            s"identifier 'r') to the interference clause on line ${interferenceClause.lineColumnPosition}.")
        }
    }

  lazy val typeOfLocation: PLocation => PType =
    attr[PLocation, PType] { case PLocation(receiver, field) =>
      typeOfIdn(receiver.id) match {
        case receiverType: PRefType =>
          entity(receiverType.id) match {
            case structEntity: StructEntity =>
              structEntity.declaration.fields.find(_.id.name == field.name) match {
                case Some(fieldDecl) => fieldDecl.typ
                case None => PUnknownType()
              }
            case _ => PUnknownType()
          }
        case _: PRegionIdType =>
          val region = usedWithRegion(receiver.id)

          region.fields.find(_.id.name == field.name) match {
            case Some(fieldDecl) => fieldDecl.typ
            case None => PUnknownType()
          }
        case _ => PUnknownType()
      }
    }

  lazy val typeOfIdn: PIdnNode => PType =
    attr[PIdnNode, PType](entity(_) match {
      case FormalArgumentEntity(decl) => decl.typ
      case FormalReturnEntity(decl) => decl.typ
      case LocalVariableEntity(decl) => decl.typ
      case LogicalVariableEntity(decl) => typeOfLogicalVariable(decl)
      case StructEntity(decl) => PRefType(decl.id)
      case _ => PUnknownType()
    })

  lazy val typeOfLogicalVariable: PLogicalVariableBinder => PType =
    attr[PLogicalVariableBinder, PType] {
      case PNamedBinder(_, Some(tipe)) => tipe
      case binder =>
        boundBy(binder) match {
          case PPointsTo(location, _) =>
            typeOfLocation(location)

          case predicateExp@PPredicateExp(id, _) =>
            val region = entity(id).asInstanceOf[RegionEntity].declaration

            outArgumentIndexOf(predicateExp)(binder) match {
              case Some(idx) => region.formalOutArgs(idx).typ
              case None => typ(region.state)
            }

          case PInterferenceClause(`binder`, set, _) =>
            typ(set) match {
              case setType: PSetType => setType.elementType
              case _ => PUnknownType()
            }

          case action: PAction if action.binds(binder) =>
            /* TODO: Replace with a proper type inference. See issue #50. */

            val region = enclosingMember(action).asInstanceOf[Option[PRegion]].get

            if (AstUtils.isBoundVariable(action.from, binder) ||
              AstUtils.isBoundVariable(action.to, binder)) {

              typ(region.state)
            } else {
              val guardOption = action.guards find {
                _.argument match {
                  case PStandardGuardArg(args) =>
                    args.exists(AstUtils.isBoundVariable(_, binder))

                  case _ => false
                }
              }

              guardOption match {
                case Some(PBaseGuardExp(guardId, PStandardGuardArg(guardArguments))) =>
                  val guard = region.guards.find(_.id.name == guardId.name).get
                  val argIdx = guardArguments.indexWhere(arg => AstUtils.isBoundVariable(arg, binder))

                  guard.formalArguments(argIdx).typ

                case _ => PUnknownType()
              }
            }

          case comprehension@PSetComprehension(namedBinder: PNamedBinder, _, _)
            if namedBinder eq binder =>

            /* TODO: Replace with a proper type inference. See issue #50. */

            comprehension.typeAnnotation match {
              case Some(_typ) =>
                _typ

              case None =>
                val name = namedBinder.id.name

                val collectOccurrencesOfFreeVariable =
                  collect[Set, PIdnExp] { case exp@PIdnExp(PIdnUse(`name`)) => exp }

                val expectedTypes =
                  collectOccurrencesOfFreeVariable(comprehension.filter).flatMap(expectedType)

                if (expectedTypes.size == 2 &&
                  expectedTypes.contains(PIntType()) &&
                  expectedTypes.contains(PFracType())) {

                  /* Resolve the choice between int and frac by preferring int */

                  PIntType()
                } else if (expectedTypes.size != 1) {
                  PUnknownType()
                } else {
                  expectedTypes.head
                }
            }

          case other => sys.error(s"Unexpectedly found $other as the binding context of $binder")
        }
    }

  lazy val boundBy: PLogicalVariableBinder => PBindingContext =
    attr[PLogicalVariableBinder, PBindingContext] {
      case tree.parent(interferenceClause: PInterferenceClause) => interferenceClause
      case tree.parent(action: PAction) => action
      case tree.parent(comprehension: PSetComprehension) => comprehension
      case tree.parent(pointsTo: PPointsTo) => pointsTo

      case tree.parent.pair(binder: PLogicalVariableBinder,
                            predicateExp @ PPredicateExp(id, arguments)) =>

        val region =
          entity(id) match {
            case regionEntity: RegionEntity =>
              regionEntity.declaration
            case _ =>
              sys.error(
                s"Logical variables cannot yet be bound by a non-region predicate. " +
                    s"Offending node is ${predicateExp.pretty} at ${predicateExp.position}.")
          }

        val idx = arguments.indices.find(arguments(_) == binder).get

        assert(
          idx >= region.formalInArgs.length,
          s"Logical variables can only be bound by out-arguments. Offending node " +
              s"${predicateExp.pretty} has illegal binder ${binder.pretty} at ${binder.position}.")

        predicateExp
    }

  /**
    * Index of the argument bound by the binder in the predicate. None is returned if the region state is bound.
    */

  lazy val outArgumentIndexOf: PPredicateExp => PLogicalVariableBinder => Option[Int] =
    paramAttr[PPredicateExp, PLogicalVariableBinder, Option[Int]](exp => binder => {
      val region =
        entity(exp.predicate) match {
          case regionEntity: RegionEntity =>
            regionEntity.declaration
          case _ =>
              sys.error(
                s"Logical variables cannot yet be bound by a non-region predicate. " +
                    s"Offending node is ${exp.pretty} at ${exp.position}.")
        }

      val args = exp.arguments

      val idx =
        args.indices.find(args(_) eq binder).get - region.formalInArgs.length

      assert(
        0 <= idx && idx < region.formalOutArgs.length + 1,
        s"Logical variables can only be bound by out-arguments. Offending node " +
            s"${exp.pretty} has illegal binder ${binder.pretty} at ${binder.position}.")

      if (idx < region.formalOutArgs.length) Some(idx) /* Regular out-argument */
      else None /* Region state out-argument */
    })

  /* TODO: Generalise poor man's type inference */

  /** What is the type of an expression?
    *
    * TODO: Replace with a proper type inference. See issue #50.
    */
  lazy val typ: PExpression => PType =
    attr[PExpression, PType](exp =>
      try {
        exp match {
          case _: PIntLit => PIntType()
          case _: PTrueLit | _: PFalseLit => PBoolType()
          case _: PNullLit => PNullType()
          case _: PFullPerm | _: PNoPerm => PFracType()

          case PIdnExp(id) => typeOfIdn(id)

          case op @ (_: PAdd | _: PSub) =>  // TODO: How to type op as PBinOp?
            val signatures: Signatures =
              Map((PFracType(), PFracType()) -> PFracType(),
                  (PIntType(),  PIntType())  -> PIntType())

            typeOrUnknown(op.asInstanceOf[PBinOp], signatures)

          case op: PMul =>
            val signatures: Signatures =
              Map((PFracType(), PFracType()) -> PFracType(),
                  (PIntType(),  PFracType()) -> PFracType(),
                  (PIntType(),  PIntType())  -> PIntType())

            typeOrUnknown(op, signatures)

          case op: PFrac =>
            val signatures: Signatures =
              Map((PFracType(), PIntType()) -> PFracType(),
                  (PIntType(),  PIntType()) -> PFracType())

            typeOrUnknown(op, signatures)

          case _: PMod | _: PDiv => PIntType()
          case _: PAnd | _: POr | _: PNot => PBoolType()
          case _: PEquals => PBoolType()

          case op @ (_: PLess | _: PAtMost | _: PGreater | _: PAtLeast) => // TODO: How to type op as PBinOp?
            val signatures: Signatures =
              Map((PFracType(), PFracType()) -> PBoolType(),
                  (PIntType(),  PIntType()) -> PBoolType())

            typeOrUnknown(op.asInstanceOf[PBinOp], signatures)

          case _: PIntSet | _: PNatSet => PSetType(PIntType())

          case explicitCollection: PExplicitCollection =>
            val typeConstructor: PType => PCollectionType =
              explicitCollection match {
                case _: PExplicitSet => PSetType
                case _: PExplicitSeq => PSeqType
              }

            explicitCollection.typeAnnotation match {
              case Some(_typ) =>
                typeConstructor(_typ)
              case None =>
                if (explicitCollection.elements.nonEmpty)
                  typeConstructor(typ(explicitCollection.elements.head))
                else
                  PUnknownType()
            }

          case explicitTuple: PExplicitTuple =>
            explicitTuple.typeAnnotation match {
              case Some(types) =>
                PTupleType(types)

              case None =>
                PTupleType(explicitTuple.elements map typ)
            }

          case explicitMap: PExplicitMap =>
            explicitMap.typeAnnotation match {
              case Some((typ1, typ2)) =>
                PMapType(typ1, typ2)

              case None =>
                if (explicitMap.elements.nonEmpty)
                  PMapType(typ(explicitMap.elements.head._1), typ(explicitMap.elements.head._2))
                else
                  PUnknownType()
            }

          case PSetComprehension(qvar, _, typeAnnotation) =>
            typeAnnotation match {
              case Some(_typ) =>
                PSetType(_typ)
              case None =>
                /* TODO: Only works if the set comprehension occurs in an action definition */
                PSetType(typeOfLogicalVariable(qvar))
            }

          case PSetUnion(left, right) =>
            (typ(left), typ(right)) match {
              case (setType1 @ PSetType(t1), PSetType(t2)) if isCompatible(t1, t2) => setType1 // TODO: Return least common supertype
              case _ => PUnknownType()
            }

          case _: PSetContains => PBoolType()
          case _: PSetSubset => PBoolType()
          case _: PSeqSize => PIntType()
          case headExp: PSeqHead => typ(headExp.seq).asInstanceOf[PCollectionType].elementType
          case tailExp: PSeqTail => typ(tailExp.seq)

          case PSeqConcat(left, right) =>
            (typ(left), typ(right)) match {
              case (seqType1 @ PSeqType(t1), PSeqType(t2)) if isCompatible(t1, t2) => seqType1 // TODO: Return least common supertype
              case _ => PUnknownType()
            }

          case getExp: PTupleGet =>
            val elementTypes = typ(getExp.tuple).asInstanceOf[PTupleType].elementTypes
            if (elementTypes.isDefinedAt(getExp.index)) {
              elementTypes(getExp.index)
            } else {
              PUnknownType() // FIXME: maybe replace with out of bounds error message
            }


          case PMapUnion(left, right) =>
            (typ(left), typ(right)) match {
              case (mapType1 @ PMapType(t1, t2), PMapType(t3, t4)) if isCompatible(t1, t3) && isCompatible(t2, t4) => mapType1 // TODO: Return least common supertype
              case _ => PUnknownType()
            }

          case PMapKeys(map) =>
            typ(map) match {
              case PMapType(t, _) => PSetType(t)
              case _ => PUnknownType()
            }

          case PMapLookup(map, _) =>
            typ(map) match {
              case PMapType(_, t) => t
              case _ => PUnknownType()
            }

          case _: PMapDisjoint => PBoolType()
          case conditional: PConditional => typ(conditional.thn)
          case unfolding: PUnfolding => typ(unfolding.body)
          case _: PPointsTo | _: PPredicateExp | _: PRegionedGuardExp | _: PBaseGuardExp | _: PTrackingResource => PBoolType()
          case binder: PLogicalVariableBinder => typeOfLogicalVariable(binder)
          case _ => PUnknownType()
        }
      } catch {
        case CyclicAttributeEvaluationException(_) => PUnknownType()
      })

  private type Signatures = Map[(PType, PType), PType]

  private def typeOrUnknown(op: PBinOp, signatures: Signatures): PType = {
    val leftType = typ(op.left)
    val rightType = typ(op.right)

    signatures.getOrElse((leftType, rightType), PUnknownType())
  }

  /**
    * What is the expected type of an expression?
    *
    * TODO: Replace with a proper type inference. See issue #50.
    */
  lazy val expectedType: PExpression => Set[PType] =
    attr[PExpression, Set[PType]] {
      case tree.parent(_: PIf | _: PWhile) => Set(PBoolType())

      case tree.parent(PAssign(id, _)) =>
        entity(id) match {
          case LocalVariableEntity(decl) => Set(decl.typ)
          case _ => Set(PUnknownType())
        }

      case tree.parent(PHeapRead(id, _)) => Set(typeOfIdn(id))

      case tree.parent(PHeapWrite(location, _)) => Set(typeOfLocation(location))

      case e @ tree.parent(PEquals(lhs, rhs)) =>
        /* Given an equality lhs == rhs, the expected type of the lhs is the type of the rhs
         * and vice versa.
         * This, however, can result in a cycle; in particular, if lhs and rhs denote the
         * same variable (whose type is to be determined). In this case, Kiama throws an
         * IllegalStateException and we return PUnknownType.
         */
        try {
          if (e eq lhs) Set(typ(rhs))
          else Set(typ(lhs))
        } catch {
          case CyclicAttributeEvaluationException(_) => Set(PUnknownType())
        }

      case tree.parent(_: PAdd | _: PSub | _: PMul) => Set(PIntType(), PFracType())
      case tree.parent(_: PMod | _: PDiv) => Set(PIntType())
      case tree.parent(_: PAnd | _: POr | _: PNot) => Set(PBoolType())

      case left  @ tree.parent(frac: PFrac) if frac.left  eq left  => Set(PIntType(), PFracType())
      case right @ tree.parent(frac: PFrac) if frac.right eq right => Set(PIntType())

      case tree.parent(_: PLess | _: PAtMost | _: PGreater | _: PAtLeast) =>
        Set(PIntType(), PFracType())

      case cnd @ tree.parent(conditional: PConditional) if cnd eq conditional.cond =>
        Set(PBoolType())

      case els @ tree.parent(conditional: PConditional) if els eq conditional.els =>
        Set(typ(conditional.thn))

      case set @ tree.parent(contains: PSetContains) if set eq contains.set =>
        Set(PSetType(typ(contains.element)))

      /* TODO: Unification is needed for handling the next cases, which require type variables */
      // case tree.parent(_: PSetContains) => /* TODO: Return set<T> */
      // case tree.parent(_: PSetUnion) => /* TODO: Return set<T> */
      // case tree.parent (_: PTupleGet) => /* TODO: Return pairN<TS> */
      // case tree.parent (_: PNPairGFet) => /* TODO: Return pairN<TS> */
      // case tree.parent(_: PMapDisjoint | _: PMapUnion) => /* TODO: Return map<T1, T2> */
      // case tree.parent(_: PMapKeys) => /* TODO: Return set<T> */
      // case tree.parent(_: PMapLookup) => /* TODO: Return map<key-type, T> */

      case lvl @ tree.parent(proc: PProcedure) if proc.level.contains(lvl) =>
        Set(PIntType())

      case _ =>
        /* Returning unknown expresses that no particular type is expected */
        Set(PUnknownType())
    }

  lazy val atomicity: PStatement => AtomicityKind =
    attr[PStatement, AtomicityKind] {
      case _: PGhostStatement => AtomicityKind.Atomic
      case stmt if isGhost(stmt) => AtomicityKind.Atomic

      case _: PAssign => AtomicityKind.Nonatomic

      case newStmt: PNewStmt =>
        entity(newStmt.constructor) match {
          case _: StructEntity => AtomicityKind.Nonatomic
          case _: RegionEntity => AtomicityKind.Atomic
          case other =>
            sys.error(s"Implementation missing for $other (of class ${other.getClass.getSimpleName})")
        }

      case seq: PSeqComp =>
        seq.components.filterNot(isGhost) match {
          case Seq() => AtomicityKind.Atomic
          case Seq(s) => atomicity(s)
          case _ => AtomicityKind.Nonatomic
        }

      case _: PIf | _: PWhile => AtomicityKind.Nonatomic

      case _: PSkip => AtomicityKind.Atomic
      case _: PHeapWrite => AtomicityKind.Atomic
      case _: PHeapRead => AtomicityKind.Atomic

      case _: PMakeAtomic => AtomicityKind.Atomic
      case _: PUpdateRegion => AtomicityKind.Atomic
      case _: PUseAtomic => AtomicityKind.Atomic
      case _: POpenRegion => AtomicityKind.Atomic

      case call: PProcedureCall =>
        val callee = entity(call.procedure).asInstanceOf[ProcedureEntity].declaration

        callee.atomicity match {
          case PNonAtomic() | PMakeAbstractAtomic() => AtomicityKind.Nonatomic
          case PPrimitiveAtomic() | PAbstractAtomic() => AtomicityKind.Atomic
        }

      case _: PFork | _: PParallelCall => AtomicityKind.Nonatomic
    }

  lazy val expectedAtomicity: PStatement => AtomicityKind =
    attr[PStatement, AtomicityKind ] {
      case tree.parent(_: PIf | _: PWhile | _: PFork | _: PParallelCall ) => AtomicityKind.Nonatomic
      case tree.parent(_: PNewStmt) => AtomicityKind.Nonatomic

      case tree.parent(p@ PSeqComp(first, second)) =>
        if (isGhost(first) || isGhost(second)) expectedAtomicity(p)
        else AtomicityKind.Nonatomic

      case tree.parent(_: PMakeAtomic) => AtomicityKind.Nonatomic
      case tree.parent(_: PUpdateRegion) => AtomicityKind.Atomic
      case tree.parent(_: PUseAtomic) => AtomicityKind.Atomic
      case tree.parent(_: POpenRegion) => AtomicityKind.Atomic

      case tree.parent(procedure: PProcedure) =>
        /* TODO: Unify with code above */
        procedure.atomicity match {
          case PNonAtomic() | PMakeAbstractAtomic() => AtomicityKind.Nonatomic
          case PPrimitiveAtomic() | PAbstractAtomic() => AtomicityKind.Atomic
        }

      case of @ tree.parent(parent) =>
        sys.error(  s"Unsupported: determining the expected atomicity of '$of' "
                  + s"(class: ${of.getClass.getSimpleName}) in the context of '$parent' "
                  + s"(class: ${parent.getClass.getSimpleName})")
    }

  lazy val isFirstStatement: PStatement => Boolean =
    attr[PStatement, Boolean] {
      case n@ tree.parent(p@ PSeqComp(left, _)) => n == left && isFirstStatement(p)
      case _ => true
    }

  lazy val nextStatement: PStatement => Option[PStatement] =
    attr[PStatement, Option[PStatement]] {
      case n@ tree.parent(p@ PSeqComp(left, right)) => if (n == left) Some(right) else nextStatement(p)
      case _ => None
    }

  lazy val firstStatement: PStatement => PStatement =
    attr[PStatement, PStatement] {
      case PSeqComp(left, _) => firstStatement(left)
      case s => s
    }

  lazy val nextActualNonSeqStatement: PStatement => Option[PStatement] =
    attr[PStatement, Option[PStatement]] { s =>
      val s2 = firstStatement(s)
      if (isGhost(s2)) {
        nextStatement(s2).flatMap(nextActualNonSeqStatement)
      } else {
        Some(s2)
      }
    }

  lazy val freeVariables: PExpression => ListSet[PIdnUse] =
    attr[PExpression, ListSet[PIdnUse]] {
      case PIdnExp(id) => ListSet(id)

      case bindingContext: PExpression with PBindingContext =>
        bindingContext match {
          case PSetComprehension(qvar, filter, _) =>
            freeVariables(filter) - PIdnUse(qvar.id.name)
          case exp: PPredicateExp =>
//            Set(arguments flatMap freeVariables :_*)
            sys.error(s"Implementation missing for $exp (of class ${exp.getClass.getSimpleName})")
          case PPointsTo(location, value) =>
            ListSet(location.receiver.id) ++ (freeVariables(value) -- boundVariables(value))
        }

      case _: PIntLit => ListSet.empty
      case _: PNullLit => ListSet.empty
      case _: PTrueLit | _: PFalseLit => ListSet.empty
      case _: PFullPerm | _: PNoPerm => ListSet.empty
      case _: PIntSet | _: PNatSet => ListSet.empty

      case explicitCollection: PExplicitCollection =>
        explicitCollection.elements.view.flatMap(freeVariables).to(ListSet)

      case PSeqSize(seq) => freeVariables(seq)
      case PSeqHead(seq) => freeVariables(seq)
      case PSeqTail(seq) => freeVariables(seq)

      case op: PUnOp => freeVariables(op.operand)
      case op: PBinOp => freeVariables(op.left) ++ freeVariables(op.right)

      case PConditional(cond, thn, els) =>
        freeVariables(cond) ++ freeVariables(thn) ++ freeVariables(els)

      case PUnfolding(predicate, body) =>
        freeVariables(predicate) ++ freeVariables(body)

      case PRegionedGuardExp(_, regionId, guardArg) =>
        ListSet(regionId.id) ++ guardArg.arguments.view.flatMap(freeVariables).to(ListSet)

      case PBaseGuardExp(_, guardArg) => guardArg.arguments.view.flatMap(freeVariables).to(ListSet)

      case PDiamond(regionId) => ListSet(regionId)

      case PRegionUpdateWitness(regionId, from, to) =>
        ListSet(regionId) ++ freeVariables(from) ++ freeVariables(to)

      case _: PAnonymousBinder => ListSet.empty

      case other =>
        sys.error(s"Implementation missing for $other (of class ${other.getClass.getSimpleName})")
    }

  lazy val boundVariables: PExpression => ListSet[PIdnDef] =
    /* TODO: check whether or not the current behaviour is intended. */
    attr[PExpression, ListSet[PIdnDef]] {
      case PNamedBinder(id, _) => ListSet(id)
      case _ => ListSet.empty
    }

  /** Path conditions under which an expression occurs.
    * Currently, only conditionals are considered as path conditions. Possible extensions could be short-circuiting
    * conjunctions/disjunctions, or unfolding expressions.
    */
  lazy val pathConditions: PExpression => Vector[PExpression] =
    attr {
      case tree.parent.pair(n, exp @ PConditional(cnd, _, _)) if n eq cnd =>
        // Current node (n) is a conditional's condition (cnd)
        pathConditions(exp)
      case tree.parent.pair(n, exp @ PConditional(cnd, thn, _)) if n eq thn =>
        // Current node (n) is a conditional's then-branch (thn)
        pathConditions(exp) :+ cnd
      case tree.parent.pair(n, exp @ PConditional(cnd, _, els)) if n eq els =>
        // Current node (n) is a conditional's else-branch (els)
        val negatedCnd = PNot(cnd)
          // WARNING: Newly created PNot isn't in the tree structure Kiama maintains. This may cause problems
          // if Kiama is later on used to traverse the PNot.
        VoilaGlobalState.positions.dupPos(cnd, negatedCnd)
        pathConditions(exp) :+ negatedCnd
      case tree.parent(exp: PExpression) =>
        pathConditions(exp)
      case _ =>
        Vector.empty
    }

  /** Similar to Kiama's [[checkUse()]]: if provider returns a V, then check(V) is executed.
    * If provider throws a ClassCastException, the latter is caught and discarded, and check is
    * not executed.
    */
  private def checkWith[V](provider: => V)(check: V => Messages): Messages = {
    var providedValue: Option[V] = None

    try {
      providedValue = Some(provider) // Execute provider
    }catch {
      case _: ClassCastException => // Do nothing
    }

    providedValue.fold(noMessages)(check)
  }

  private implicit def defs2UsesSets(xs: ListSet[PIdnDef]): ListSet[PIdnUse] =
    xs.map(idndef => PIdnUse(idndef.name))

  private object CyclicAttributeEvaluationException {
    def unapply(exception: Exception): Option[IllegalStateException] = {
      exception match {
        case ex: IllegalStateException if ex.getMessage.toLowerCase.startsWith("cycle detected") =>
          Some(ex)
        case _ => None
      }
    }
  }
}

sealed trait LogicalVariableContext

object LogicalVariableContext {
  case object Interference extends LogicalVariableContext
  case object Precondition extends LogicalVariableContext
  case object Postcondition extends LogicalVariableContext
  case object Invariant extends LogicalVariableContext
  case object Procedure extends LogicalVariableContext
  case object Region extends LogicalVariableContext
  case object Predicate extends LogicalVariableContext
}

sealed trait AtomicityKind

object AtomicityKind {
  case object Nonatomic extends AtomicityKind
  case object Atomic extends AtomicityKind
}

private sealed trait RegionIdUsage {
  def id: PIdnNode
  def region: PRegion
  def arguments: Vector[PAstNode]
  def source: PAstNode

  override lazy val toString: String =
    s"${id.name} -> ${region.id}${arguments.mkString("(", ",", ")")} [${source.position}]"
}

private final case class RegionDeclarationUsage(id: PIdnNode, region: PRegion) extends RegionIdUsage {
  val arguments: Vector[PIdnDef] = region.formalInArgs.map(_.id)
  val source: PRegion = region
}

private final case class RegionPredicateUsage(id: PIdnNode, region: PRegion, source: PPredicateExp) extends RegionIdUsage {
  val arguments: Vector[PExpression] = source.arguments.take(region.formalInArgs.length)
}

private final case class NewStmtUsage(id: PIdnNode, region: PRegion, source: PNewStmt) extends RegionIdUsage {
  val arguments: Vector[PExpression] = source.arguments
}
