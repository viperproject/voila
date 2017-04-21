/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import viper.silver.ast.FieldAccess
import viper.voila.frontend._
import viper.silver.{ast => vpr}

trait Translator[F, T] {
  def translate(source: F): T
}

class PProgramToViperTranslator(val semanticAnalyser: SemanticAnalyser)
    extends Translator[VoilaTree, vpr.Program]
       with MainTranslatorComponent
       with HeapAccessTranslatorComponent
       with RegionTranslatorComponent

trait MainTranslatorComponent { this: PProgramToViperTranslator =>
  private val returnVarName = "ret"

  private def intSet(pos: vpr.Position = vpr.NoPosition, info: vpr.Info = vpr.NoInfo) =
    vpr.FuncApp.apply("IntSet", Vector.empty)(pos, info, vpr.SetType(vpr.Int), Vector.empty)

  private def natSet(pos: vpr.Position = vpr.NoPosition, info: vpr.Info = vpr.NoInfo) =
    vpr.FuncApp("NatSet", Vector.empty)(pos, info, vpr.SetType(vpr.Int), Vector.empty)

  def translate(tree: VoilaTree): vpr.Program = {
    val members: Vector[vpr.Member] = (
         heapLocations(tree)
      ++ (tree.root.regions flatMap translate)
      ++ (tree.root.predicates map translate)
      ++ (tree.root.procedures map translate)
    )

    val fields = members collect { case f: vpr.Field => f }
    val predicates = members collect { case f: vpr.Predicate => f }
    val functions = members collect { case f: vpr.Function => f }
    val methods = members collect { case f: vpr.Method => f }

    println(methods)

    vpr.Program(
      domains = Nil,
      fields = fields,
      functions = functions,
      predicates = predicates,
      methods = methods
    )()
  }

  def translate(member: PMember): vpr.Member =
    member match {
      case r: PRegion => translate(r)
      case p: PPredicate => translate(p)
      case p: PProcedure => translate(p)
    }

  def translate(predicate: PPredicate): vpr.Predicate = {
    vpr.Predicate(
      name = predicate.id.name,
      formalArgs = predicate.formalArgs map translate,
      _body = Some(translate(predicate.body))
    )()
  }

  def translate(procedure: PProcedure): vpr.Method = {
    val formalReturns =
      procedure.typ match {
        case PVoidType() => Nil
        case other => Seq(vpr.LocalVarDecl(returnVarName, translateNonVoid(other))())
      }

    val pres = (
         procedure.pres.map(translate)
      ++ procedure.inters.map(translate)
    )

    vpr.Method(
      name = procedure.id.name,
      formalArgs = procedure.formalArgs map translate,
      formalReturns = formalReturns,
      _pres = pres,
      _posts = procedure.posts map translate,
      _locals = procedure.locals map translate,
      _body = vpr.Seqn(procedure.body map translate)()
    )()
  }

  def translate(declaration: PFormalArgumentDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translateNonVoid(declaration.typ))()

  def translate(interference: PInterferenceClause): vpr.AnySetContains = {
    /* TODO: Use correct type */
    val lv = vpr.LocalVar(interference.variable.name)(typ = vpr.Int)
    val set = translate(interference.set)

    vpr.AnySetContains(lv, set)()
  }

  def translate(statement: PStatement): vpr.Stmt = statement match {
    case PBlock(stmts) =>
      vpr.Seqn(stmts map translate)()
    case PIf(cond, thn, els) =>
      vpr.If(translate(cond), translate(thn), translate(els))()
    case PWhile(cond, body) =>
      vpr.While(translate(cond), Nil, Nil, translate(body))()
    case PAssign(lhs, rhs) =>
      /* TODO: Use correct type */
      vpr.LocalVarAssign(vpr.LocalVar(lhs.name)(typ = vpr.Int), translate(rhs))()
    case read: PHeapRead =>
      translate(read)
    case write: PHeapWrite =>
      translate(write)
  }

  def translate(expression: PExpression): vpr.Exp = expression match {
    case PTrueLit() => vpr.TrueLit()()
    case PFalseLit() => vpr.FalseLit()()
    case PIntLit(n) => vpr.IntLit(n)()
    case PEquals(left, right) => vpr.EqCmp(translate(left), translate(right))()
    case PAnd(left, right) => vpr.And(translate(left), translate(right))()
    case POr(left, right) => vpr.Or(translate(left), translate(right))()
    case PNot(operand) => vpr.Not(translate(operand))()
    case PLess(left, right) => vpr.LtCmp(translate(left), translate(right))()
    case PAtMost(left, right) => vpr.LeCmp(translate(left), translate(right))()
    case PGreater(left, right) => vpr.GtCmp(translate(left), translate(right))()
    case PAtLeast(left, right) => vpr.GeCmp(translate(left), translate(right))()
    case PAdd(left, right) => vpr.Add(translate(left), translate(right))()
    case PSub(left, right) => vpr.Sub(translate(left), translate(right))()
    case PConditional(cond, thn, els) => vpr.CondExp(translate(cond), translate(thn), translate(els))()
    case PExplicitSet(elements) => vpr.ExplicitSet(elements map translate)()
    case PIntSet() => intSet()
    case PNatSet() => natSet()

    case pointsTo: PPointsTo => translate(pointsTo)

    case PPredicateExp(id, args) =>
      semanticAnalyser.entity(id) match {
        case _: PredicateEntity =>
//          val vprArgs = args map {
//            case Left(_: PLogicalVariableDecl) => ???
//            case Right(exp) => translate(exp)
////            case entity: LogicalVariableEntity => translateUseOf(entity.declaration)
//          }

          vpr.PredicateAccess(args map translate, id.name)(vpr.NoPosition, vpr.NoInfo)

        case RegionEntity(decl) =>
          translateUseOf(decl, args)

        case other =>
          sys.error(s"Not yet supported: $other")
      }

    case PIdnExp(id) =>
      semanticAnalyser.entity(id) match {
        case entity: LogicalVariableEntity => translateUseOf(entity.declaration)
        case _ =>
          /* TODO: Use correct type */
          vpr.LocalVar(id.name)(typ = vpr.Int)
      }

    case guard: PGuardExp => translate(guard)

  }

  def translate(declaration: PLocalVariableDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translateNonVoid(declaration.typ))()

  def translateNonVoid(typ: PType): vpr.Type = typ match {
    case PIntType() => vpr.Int
    case PBoolType() => vpr.Bool
    case PSetType(elementType) => vpr.SetType(translateNonVoid(elementType))
    case PRefType(_) => vpr.Ref
    case PRegionIdType() => vpr.Ref
    case unsupported@(_: PVoidType | _: PUnknownType) =>
      sys.error(s"Cannot translate type '$unsupported'")
  }
}

trait RegionTranslatorComponent { this: PProgramToViperTranslator =>
  def regionStateFunctionName(region: PRegion): String =
    s"${region.id.name}_state"

  def guardPredicateName(guard: PGuardDecl, region: PRegion): String =
    s"${region.id.name}_${guard.id.name}"

  def guardPotentiallyHeldFunctionName(guard: PGuardDecl, region: PRegion): String =
    s"${region.id.name}_${guard.id.name}_potentiallyHeldByEnvironment"

def guardTransitiveClosureFunctionName(guard: PGuardDecl, region: PRegion): String =
    s"${region.id.name}_${guard.id.name}_transitiveClosure"

//  def guards(tree: VoilaTree): Vector[vpr.Predicate] = {
//    tree.root.regions flatMap (region =>
//      region.guards map (guard =>
//        vpr.Predicate(
//          name = regionGuardName(guard, region),
//          formalArgs = Vector(vpr.LocalVarDecl("$r", translateNonVoid(PRegionIdType()))()),
//          _body = None
//        )()
//      )
//    )
//  }

  def translate(region: PRegion): Vector[vpr.Member] = {
    val formalRegionArg = translate(region.regionId)
    val formalRegularArgs = region.formalArgs map translate

    val regionStateType = translateNonVoid(semanticAnalyser.typ(region.state))
//    val formalStateArg = vpr.LocalVarDecl("$s", regionStateType)()

    val regionPredicateName = region.id.name

    /* predicate region(id, args) { interpretation } */
    val regionPredicate =
      vpr.Predicate(
        name = regionPredicateName,
        formalArgs = formalRegionArg +: formalRegularArgs,
        _body = Some(translate(region.interpretation))
      )()

    /* predicate region_G(r: RegionId) for each guard G */
    val guardPredicates =
      region.guards map (guard =>
        vpr.Predicate(
          name = guardPredicateName(guard, region),
          formalArgs = Vector(vpr.LocalVarDecl("$r", translateNonVoid(PRegionIdType()))()),
          _body = None
        )())

    /* function region_G_potentiallyHeldByEnvironment(r: RegionId, p: Perm)
     *   {...}
     * for each guard G
     */
    val guardPotentiallyHeldFunctions =
      region.guards map (guard => {
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
        )()})

    val guardTransitiveClosureFunctions =
      region.guards map (guard => {
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
        )()})

    /* acc(region(id, args)) */
    val regionPredicateAccess =
      vpr.PredicateAccessPredicate(
        loc = vpr.PredicateAccess(
                  args = formalRegionArg.localVar +: formalRegularArgs.map(_.localVar),
                  predicateName = regionPredicateName
              )(pos = vpr.NoPosition, info = vpr.NoInfo),
        perm = vpr.FullPerm()()
      )()

    val stateFunctionBody =
      vpr.Unfolding(
        acc = regionPredicateAccess,
        body = translate(region.state)
      )()

    /* function region_state(id, args)
     *   requires region(id, args)
     * { state }
     */
    val stateFunction =
      vpr.Function(
        name = regionStateFunctionName(region),
        formalArgs = formalRegionArg +: formalRegularArgs,
        typ = regionStateType,
        _pres = Vector(regionPredicateAccess),
        _posts = Vector.empty,
        _body = Some(stateFunctionBody)
      )()

    (   guardPredicates
     ++ guardPotentiallyHeldFunctions
     ++ guardTransitiveClosureFunctions
     ++  Vector(
            regionPredicate,
            stateFunction))
  }

  def translateUseOf(region: PRegion, args: Vector[PExpression]): vpr.Exp = {
    val vprRegionId = translate(args.head)

    val (vprRegularArgs, Seq(vprStateValue)) =
      args.tail.map(translate).splitAt(args.length - 2)

    val vprRegionArguments = vprRegionId +: vprRegularArgs

    val vprRegionArgumentDecls =
      /* TODO: Needed in order to construct an instance of vpr.FuncApp.
       *       Should be taken from the declaration of the region state function.
       */
      vprRegionArguments.map(a => vpr.LocalVarDecl("x", a.typ)())

    val vprStateConstraint =
      vpr.EqCmp(
        vpr.FuncApp(
          funcname = regionStateFunctionName(region),
          args = vprRegionArguments
        )(
          pos = vpr.NoPosition,
          info = vpr.NoInfo,
          typ = vprStateValue.typ,
          formalArgs = vprRegionArgumentDecls
        ),
        vprStateValue
      )()

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
        val name = guardPredicateName(guardDecl, region)

        val guardPredicateAccess =
          vpr.PredicateAccessPredicate(
            loc = vpr.PredicateAccess(
                    args = Vector(translate(PIdnExp(guardExp.regionId))),
                    predicateName = name
                  )(pos = vpr.NoPosition, info = vpr.NoInfo),
            perm = vpr.FullPerm()()
          )()

        guardPredicateAccess
    }
  }
}

trait HeapAccessTranslatorComponent { this: PProgramToViperTranslator =>
  private def heapLocationAsField(typ: PType): vpr.Field =
    vpr.Field(s"$$h_$typ", translateNonVoid(typ))()

  private def referencedType(id: PIdnNode): PType =
    semanticAnalyser.referencedType(semanticAnalyser.typeOfIdn(id))

  def heapLocations(tree: VoilaTree): Vector[vpr.Field] = {
    tree.nodes.collect {
      case access: PHeapAccess => heapLocationAsField(referencedType(access.location))
      case pointsTo: PPointsTo => heapLocationAsField(referencedType(pointsTo.id))
    }.distinct
  }

  def translate(read: PHeapRead): vpr.Stmt = {
    val voilaType = referencedType(read.location)
    val viperType = translateNonVoid(voilaType)

    val rcvr = vpr.LocalVar(read.location.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)
    val lv = vpr.LocalVar(read.lhs.name)(typ = viperType)

    vpr.LocalVarAssign(lv, vpr.FieldAccess(rcvr, fld)())()
  }

  def translate(write: PHeapWrite): vpr.Stmt = {
    val voilaType = referencedType(write.location)
//    val viperType = translateNonVoid(voilaType)

    val rcvr = vpr.LocalVar(write.location.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)

    vpr.FieldAssign(vpr.FieldAccess(rcvr, fld)(), translate(write.rhs))()
  }

  def translate(pointsTo: PPointsTo): vpr.Exp = {
    val voilaType = referencedType(pointsTo.id)

    val rcvr = vpr.LocalVar(pointsTo.id.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)
    val fldacc = vpr.FieldAccess(rcvr, fld)()

    val fldvalcnstr = pointsTo.value match {
      case Left(decl: PLogicalVariableDecl) => vpr.TrueLit()()
      case Right(exp) => vpr.EqCmp(fldacc, translate(exp))()
    }

    vpr.And(
      vpr.FieldAccessPredicate(fldacc, vpr.FullPerm()())(),
      fldvalcnstr
    )()
  }

  def translateUseOf(declaration: PLogicalVariableDecl): FieldAccess = {
//    println("\n[translateUseOf]")
//    println(s"  declaration = $declaration")
    val boundTo = semanticAnalyser.boundTo(declaration)
    val voilaType = semanticAnalyser.typeOfIdn(declaration.id)
//    val voilaType = referencedType(entity.declaration.id)
//    println(s"  voilaType = $voilaType")

    val rcvr = vpr.LocalVar(boundTo.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)

    vpr.FieldAccess(rcvr, fld)()
  }
}
