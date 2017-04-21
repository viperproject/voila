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
    case PCallExp(id, args) =>
      semanticAnalyser.entity(id) match {
        case _: PredicateEntity =>
          vpr.PredicateAccess(args map translate, id.name)(vpr.NoPosition, vpr.NoInfo)
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
    case PExplicitSet(elements) => vpr.ExplicitSet(elements map translate)()
    case PIntSet() => intSet()
    case PNatSet() => natSet()
    case pointsTo: PPointsTo => translate(pointsTo)
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
        name = s"${region.id.name}_state",
        formalArgs = formalRegionArg +: formalRegularArgs,
        typ = regionStateType,
        _pres = Vector(regionPredicateAccess),
        _posts = Vector.empty,
        _body = Some(stateFunctionBody)
      )()

    Vector(
      regionPredicate,
      stateFunction
    )
  }
}

trait HeapAccessTranslatorComponent { this: PProgramToViperTranslator =>
  private def heapLocationAsField(typ: PType): vpr.Field =
    vpr.Field(s"$$h_$typ", translateNonVoid(typ))()

  private def referencedType(id: PIdnNode): PType = {
    semanticAnalyser.referencedType(semanticAnalyser.typeOfIdn(id))
//    val entity = semanticAnalyser.entity(id).asInstanceOf[RegularEntity]
//    val decl = entity.declaration.asInstanceOf[PTypedDeclaration]
//    val typ = decl.typ.asInstanceOf[PRefType]
//
//    typ.referencedType
  }

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
