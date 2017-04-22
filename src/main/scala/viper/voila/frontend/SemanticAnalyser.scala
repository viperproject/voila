/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.==>
import org.bitbucket.inkytonik.kiama.attribution.{Attribution, Decorators}
import org.bitbucket.inkytonik.kiama.rewriting.Rewriter._
import org.bitbucket.inkytonik.kiama.util.{Entity, MultipleEntity, UnknownEntity}
import org.bitbucket.inkytonik.kiama.util.Messaging.{check, checkUse, collectMessages, Messages, message}

class SemanticAnalyser(tree: VoilaTree) extends Attribution {
  val symbolTable = new SymbolTable()
  import symbolTable._

  val decorators = new Decorators(tree)
  import decorators._

  lazy val errors: Messages =
    collectMessages(tree) {
      case decl: PIdnDef if entity(decl) == MultipleEntity() =>
        message(decl, s"${decl.name} is declared more than once")

      case use: PIdnUse if entity(use) == UnknownEntity() =>
        message(use, s"${use.name} is not declared")

      case exp: PExpression if typ(exp) == PUnknownType() =>
        message(exp, s"$exp could not be typed")

      case PAssign(lhs, _) if !entity(lhs).isInstanceOf[LocalVariableEntity] =>
        message(lhs, s"Cannot assign to ${lhs.name}")

      case PHeapRead(lhs, rhs) =>
        check(entity(lhs)) {
          case LocalVariableEntity(lhsDecl) =>
            val rhsTyp = typeOfIdn(rhs)

            message(
              rhs,
              s"Type error: expected ${lhsDecl.typ}* but got $rhsTyp",
              !isCompatible(referencedType(rhsTyp), lhsDecl.typ))
//            entity(rhs) match {
//              case RegularEntity(rhsDecl) =>
//                val rhsType = typ
//                val messages1 =
//                  message(
//                    rhs,
//                    s"Type error: expected a reference type, but found ${rhsDecl.typ}",
//                    !rhsDecl.typ.isInstanceOf[PRefType])
//
//                val messages2 =
//                  message(
//                    rhs,
//                    s"Type error: expected ${lhsDecl.typ}* but got ${rhsDecl.typ}",
//                    !isCompatible(referencedType(rhsDecl.typ), lhsDecl.typ))
//
//                messages1 ++ messages2
//            }


          case other =>
            message(lhs, s"Type error: expected a local variable, but found $other")
        }

//        checkUse(entity(lhs)) { case TypedVariableEntity(lhsDecl) =>
//          checkUse(entity(rhs)) { case TypedVariableEntity(rhsDecl) => (
//               message(
//                 rhs,
//                 s"Type error: expected a reference type, but found ${rhsDecl.typ}",
//                 !rhsDecl.typ.isInstanceOf[PRefType])
//            ++
//               message(
//                 rhs,
//                 s"Type error: expected ${lhsDecl.typ}* but got ${rhsDecl.typ}",
//                 !isCompatible(referencedType(rhsDecl.typ), lhsDecl.typ)))
//          }
//        }

      case PHeapWrite(lhs, _) =>
        typeOfIdn(lhs) match {
          case _: PRefType =>
            message(lhs, "????????????????", false)
            /* TODO: Check compatibility of LHS and RHS? */
          case otherType =>
            message(
              lhs,
              s"Type error: expected a reference type, but found $otherType")
        }

//        checkUse(entity(lhs)) { case TypedVariableEntity(lhsDecl) =>
//           message(
//             lhs,
//             s"Type error: expected a reference type, but found ${lhsDecl.typ}",
//             !lhsDecl.typ.isInstanceOf[PRefType])
//        }

      case exp: PExpression => (
           message(
              exp,
              s"Type error: expected ${expectedType(exp)} but got ${typ(exp)}",
              !isCompatible(typ(exp), expectedType(exp)))
        ++
           check(exp) {
              case PIdnExp(id) =>
                checkUse(entity(id)) {
                  case _: ProcedureEntity =>
                    message(id, "Cannot refer to procedures directly")
                }

              case PPredicateExp(id, args) =>
                checkUse(entity(id)) {
                  case PredicateEntity(decl) =>
                    reportArgumentLengthMismatch(decl.id, decl.formalArgs.length, args.length)

                  case RegionEntity(decl) =>
                    /* A region predicate has the following arguments: region id, regular arguments,
                     * state. Hence, the provided argument count should be formal arguments + 2.
                     */
                    reportArgumentLengthMismatch(decl.id, decl.formalArgs.length + 2, args.length)

                  case _ =>
                    message(id, s"Cannot call ${id.name}")
                }

//              case PCall(id, args) =>
//                checkUse(entity(id)) {
//                  case ProcedureEntity(decl) =>
//                    reportArgumentLengthMismatch(decl.id, decl.formalArgs, args)
//
//                  case PredicateEntity(decl) =>
//                    reportArgumentLengthMismatch(decl.id, decl.formalArgs, args)
//
//                  case _ =>
//                    message(id, s"Cannot call ${id.name}")
//                }
          })
    }

  private def reportArgumentLengthMismatch(id: PIdnNode,
                                           formalArgCount: Int,
                                           actualArgCount: Int) = {

    message(
      id,
        s"Wrong number of arguments for '${id.name}', got $actualArgCount "
      + s"but expected $formalArgCount",
      formalArgCount != actualArgCount)
  }

  /**
    * Are two types compatible?  If either of them are unknown then we
    * assume an error has already been raised elsewhere so we say they
    * are compatible with anything. Otherwise, the two types have to be
    * the same.
    */
  def isCompatible(t1: PType, t2: PType): Boolean =
      (t1 == PUnknownType()) ||
      (t2 == PUnknownType()) ||
      (t1 == t2)

  /**
    * The entity defined by a defining occurrence of an identifier.
    * Defined by the context of the occurrence.
    */
  lazy val definedEntity: PIdnDef => Entity =
    attr {
      case tree.parent(p) =>
        p match {
          case decl: PProcedure => ProcedureEntity(decl)
          case decl: PPredicate => PredicateEntity(decl)
          case decl: PRegion => RegionEntity(decl)
          case decl: PGuardDecl => GuardEntity(decl, tree.parent.pair.unapply(decl).get._2.asInstanceOf[PRegion])
          case decl: PFormalArgumentDecl => ArgumentEntity(decl)
          case decl: PLocalVariableDecl => LocalVariableEntity(decl)
          case decl: PLogicalVariableDecl => LogicalVariableEntity(decl)
          case _ => UnknownEntity()
        }
    }

  /**
    * The environment to use to lookup names at a node. Defined to be the
    * completed defining environment for the smallest enclosing scope.
    */
  lazy val env: PAstNode => Environment =
    attr {
      // At a scope-introducing node, get the final value of the
      // defining environment, so that all of the definitions of
      // that scope are present.
      case tree.lastChild.pair(_: PProgram | _: PMember, c) =>
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
    // At the root, get a new empty environment
    case program: PProgram =>
      val topLevelBindings = (
           program.regions.map(r => r.id.name -> RegionEntity(r))
        ++ program.predicates.map(p => p.id.name -> PredicateEntity(p))
        ++ program.procedures.map(p => p.id.name -> ProcedureEntity(p)))

      val guardBindings =
        program.regions.flatMap(region =>
          region.guards.map(guard =>
            s"${guard.id.name}@${region.id.name}" -> GuardEntity(guard, region)))

      rootenv(topLevelBindings ++ guardBindings :_*)

    // At a nested scope region, create a new empty scope inside the outer
    // environment
    case scope@(_: PMember) =>
      enter(in(scope))

//    case pp: PPointsTo =>
//      println(s"pp = $pp")
//      println(s"in(pp) = ${in(pp)}")
//      in(pp)
  }

  def defenvout(out: PAstNode => Environment): PAstNode ==> Environment = {
    // When leaving a nested scope region, remove the innermost scope from
    // the environment
    case scope@(_: PMember) =>
      leave(out(scope))

    // At a defining occurrence of an identifier, check to see if it's already
    // been defined in this scope. If so, change its entity to MultipleEntity,
    // otherwise use the entity appropriate for this definition.
    case idef: PIdnDef =>
//      println(s"idef = $idef")
//      println(s"out(idef) = ${out(idef)}")
      defineIfNew(out(idef), idef.name, definedEntity(idef))
  }

  /**********************************************************
   *  TODO: Modify environment computation such that a PPredicateExp
   *          Region(a, ...)
   *        adds a binding from a to Region to the environment
   */

  /**
    * The program entity referred to by an identifier definition or use.
    */
  lazy val entity: PIdnNode => Entity =
    attr {
      case g @ tree.parent(PGuardExp(guardId, regionId)) if guardId eq g =>
        val region = usedWithRegion(regionId)
        val guardAtRegion = s"${guardId.name}@${region.id.name}"

        lookup(env(guardId), guardAtRegion, UnknownEntity())

      case n =>
        lookup(env(n), n.name, UnknownEntity())
    }


  lazy val usedWithRegion: PIdnNode => PRegion =
    attr(id => enclosingScope(id)(id) match {
      case Some(scope) =>
        val regions =
          collect[Vector, Option[PRegion]] {
            case PPredicateExp(region, PIdnExp(`id`) +: _) =>
              entity(region) match {
                case RegionEntity(decl) => Some(decl)
                case _ => None
              }
          }

        regions(scope).flatten.head

      case None =>
        ???
    })

    lazy val enclosingScope: PAstNode => PAstNode => Option[PMember] =
      paramAttr { node => {
          case member: PMember =>
            Some(member)
          case tree.parent(p) =>
            enclosingScope(node)(p)
        }
      }

  /**
    * Return the internal type of a syntactic type. In most cases they
    * are the same. The exception is class types since the class type
    * refers to the class by name, but we need to have it as a reference
    * type that refers to the declaration of that class.
    */
  def actualType(typ: PType): PType =
    typ match {
//        case ClassType(idn) =>
//            entity(idn) match {
//                case ClassEntity(decl) =>
//                    ReferenceType(decl)
//                case _ =>
//                    UnknownType()
//            }
      case _ => typ
    }

  def referencedType(typ: PType): PType =
    typ match {
      case PRefType(t) => t
      case _ => PUnknownType()
    }

  lazy val typeOfIdn: PIdnNode => PType =
    attr(entity(_) match {
      case ArgumentEntity(decl) => decl.typ
      case LocalVariableEntity(decl) => decl.typ
      case ProcedureEntity(decl) => decl.typ
      case LogicalVariableEntity(decl) =>
//        println("\n[typeOfIdn]")
//        println(s"  decl = $decl")
        val t = typeOfLogicalVariable(decl)
//        println(s"  typeOfLogicalVariable = $t")
        t
      case _ => PUnknownType()
    })

//  def typeOfIdn(idn: PIdnNode): PType =
//    entity(idn) match {
//      case ArgumentEntity(decl) => decl.typ
//      case LocalVariableEntity(decl) => decl.typ
//      case ProcedureEntity(decl) => decl.typ
//      case LogicalVariableEntity(decl) =>
//        println("\n[typeOfIdn]")
//        println(s"  decl = $decl")
//        val t = typeOfLogicalVariable(decl)
//        println(s"  typeOfLogicalVariable = $t")
//        t
//      case _ => PUnknownType()
//    }

  lazy val typeOfLogicalVariable: PLogicalVariableDecl => PType =
    attr {
      case tree.parent(pointsTo: PPointsTo) =>
        referencedType(typeOfIdn(pointsTo.id))
    }

  lazy val boundTo: PLogicalVariableDecl => PIdnNode =
    attr {
      case tree.parent(pointsTo: PPointsTo) => pointsTo.id
    }

  /**
    * What is the type of an expression?
    */
  lazy val typ: PExpression => PType =
    attr {
      case _: PIntLit => PIntType()
      case _: PTrueLit | _: PFalseLit => PBoolType()

      case PIdnExp(id) =>
//        println(s"PIdnExp(id) = PIdnExp($id)")
//        println(s"entity(id) = ${entity(id)}")
        actualType(typeOfIdn(id))
//        entity(id) match {
//          case TypedVariableEntity(decl) =>
//            println(s"actualType(decl.typ) = ${actualType(decl.typ)}")
//            actualType(decl.typ)
//          case _ => PUnknownType()
//        }

      case _: PAdd | _: PSub => PIntType()
      case _: PAnd | _: POr | _: PNot => PBoolType()
      case _: PEquals | _: PLess | _: PAtMost | _: PGreater | _: PAtLeast => PBoolType()

      case _: PIntSet | _: PNatSet => PSetType(PIntType())
      case PExplicitSet(elements) => PSetType(typ(elements.head))

      case _: PPointsTo | _: PPredicateExp | _: PGuardExp => PBoolType()

      case tree.parent.pair(_: PLogicalVariableDecl, pointsTo: PPointsTo) =>
        referencedType(typeOfIdn(pointsTo.id))

//      case logicalVarDecl: PLogicalVariableDecl =>
//        tree.parent(logicalVarDecl) match {
//          case pp: PPointsTo =>
//            ???
//        }
//        ???


//          case CallExp(_, i, _) =>
//              entity(i) match {
//                  case MethodEntity(decl) =>
//                      actualTypeOf(decl.body.tipe)
//                  case _ =>
//                      UnknownType()
//              }

      case _ => PUnknownType()
    }

  /**
    * What is the expected type of an expression?
    */
  lazy val expectedType: PExpression => PType =
    attr {
      case tree.parent(_: PIf | _: PWhile) => PBoolType()

      case tree.parent(PAssign(id, _)) =>
        entity(id) match {
          case LocalVariableEntity(decl) => actualType(decl.typ)
          case _ => PUnknownType()
        }

      case tree.parent(PHeapRead(id, _)) =>
        referencedType(typeOfIdn(id))
//        entity(id) match {
//          case TypedVariableEntity(decl) => referencedType(decl.typ)
//          case _ => PUnknownType()
//        }

      case tree.parent(PHeapWrite(id, _)) =>
        referencedType(typeOfIdn(id))
//        entity(id) match {
//          case TypedVariableEntity(decl) => referencedType(decl.typ)
//          case _ => PUnknownType()
//        }

      case e @ tree.parent(PEquals(lhs, rhs)) if e eq rhs =>
        /* The expected type of the RHS of an equality is the type of the LHS */
        typ(lhs)

      case tree.parent(_: PAdd | _: PSub) => PIntType()
      case tree.parent(_: PAnd | _: POr | _: PNot) => PBoolType()
      case tree.parent(_: PLess | _: PAtMost | _: PGreater | _: PAtLeast) => PIntType()

//      case pp: PPointsTo =>
//        println("Hit PPointsTo!")
//        println(s"pp = $pp")
//        ???

//      case e @ tree.parent(pp: PPointsTo) =>
//        println("Hit e!")
//        println(s"e = $e")
//        println(s"pp = $pp")
//        ???
//
//      case decl: PLogicalVariableDecl =>
//        println("Hit PLogicalVariableDecl!")
//        println(s"decl = $decl")
//        ???

//      case tree.parent(tree.parent.pair(decl: PLogicalVariableDecl, PPointsTo(id, _))) =>
//        println("Hit funny thing!")
//        println(s"id = $id")
//        println(s"decl = $decl")
//        ???


//        case e @ tree.parent(CallExp(base, u, _)) if base eq e =>
//            UnknownType()
//
//        case e @ tree.parent(CallExp(_, u, _)) =>
//            entity(u) match {
//                case MethodEntity(decl) =>
//                    expTypeOfArg(decl, tree.index(e))
//
//                case _ =>
//                    // No idea what is being called, so no type constraint
//                    UnknownType()
//            }

//        case tree.parent(tree.parent.pair(_ : Result, MethodBody(t, _, _, _, _))) =>
//            actualTypeOf(t)

      case _ =>
        /* Returning unknown expresses that no particular type is expected */
        PUnknownType()
    }
}
