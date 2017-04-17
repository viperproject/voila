/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import viper.voila.frontend._
import viper.silver.{ast => vpr}

trait Translator[F, T] {
  def translate(source: F): T
}

class PProgramToViperTranslator(val semanticAnalyser: SemanticAnalyser)
    extends Translator[VoilaTree, vpr.Program] {

  private val returnVarName = "ret"

  private def intSet(pos: vpr.Position = vpr.NoPosition, info: vpr.Info = vpr.NoInfo, errT: vpr.ErrorTrafo =vpr.NoTrafos) =
    vpr.FuncApp.apply("IntSet", Vector.empty)(pos, info, vpr.SetType(vpr.Int), Vector.empty, errT)

  private def natSet(pos: vpr.Position = vpr.NoPosition, info: vpr.Info = vpr.NoInfo, errT: vpr.ErrorTrafo = vpr.NoTrafos) =
    vpr.FuncApp("NatSet", Vector.empty)(pos, info, vpr.SetType(vpr.Int), Vector.empty, errT)

  val heapAccessTranslator = new HeapAccessTranslatorComponent(this)

  def translate(tree: VoilaTree): vpr.Program = {
    val fields = heapAccessTranslator.heapLocations(tree)
    val predicates = tree.root.predicates map translate
    val methods = tree.root.procedures map translate

    vpr.Program(
      domains = Nil,
      fields = fields,
      functions = Nil,
      predicates = predicates,
      methods = methods)()
  }

  def translate(member: PMember): vpr.Member =
    member match {
      case p: PPredicate => translate(p)
      case p: PProcedure => translate(p)
    }

  def translate(predicate: PPredicate): vpr.Predicate = {
    vpr.Predicate(
      name = predicate.id.name,
      formalArgs = predicate.formalArgs map translate,
      _body = Some(translate(predicate.body)))()
  }

  def translate(procedure: PProcedure): vpr.Method = {
    val formalReturns =
      procedure.typ match {
        case PVoidType() => Nil
        case other => Seq(vpr.LocalVarDecl(returnVarName, translateNonVoid(procedure.typ))())
      }

    val pres = (
         procedure.pres.map(translate)
      ++ procedure.inters.map(translate))

    vpr.Method(
      name = procedure.id.name,
      formalArgs = procedure.formalArgs map translate,
      formalReturns = formalReturns,
      _pres = pres,
      _posts = procedure.posts map translate,
      _locals = procedure.locals map translate,
      _body = vpr.Seqn(procedure.body map translate)())()
  }

  def translate(declaration: PFormalArgumentDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translateNonVoid(declaration.typ))()

  def translate(interference: InterferenceClause): vpr.AnySetContains = {
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
      heapAccessTranslator.translate(read)
    case write: PHeapWrite =>
      heapAccessTranslator.translate(write)
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
        case PredicateEntity(decl) =>
          vpr.PredicateAccess(args map translate, id.name)(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)
        case other =>
          sys.error(s"Not yet supported: $other")
      }
//      /* TODO: Use correct type */
//      /* TODO: Use correct formal args  */
//      vpr.FuncApp(id.name, args map translate)(vpr.NoPosition, vpr.NoInfo, typ = vpr.Int, formalArgs = Nil, vpr.NoTrafos)
    case PIdnExp(id) =>
      /* TODO: Use correct type */
      vpr.LocalVar(id.name)(typ = vpr.Int)
    case PExplicitSet(elements) => vpr.ExplicitSet(elements map translate)()
    case PIntSet() => intSet()
    case PNatSet() => natSet()
  }

  def translate(declaration: PLocalVariableDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translateNonVoid(declaration.typ))()

  def translateNonVoid(typ: PType): vpr.Type = typ match {
    case PIntType() => vpr.Int
    case PBoolType() => vpr.Bool
    case PRefType(_) => vpr.Ref
    case PRegionIdType() => vpr.Ref
    case unsupported@(_: PVoidType | _: PUnknownType) =>
      sys.error(s"Cannot translate type '$unsupported'")
  }
}

class HeapAccessTranslatorComponent(translator: PProgramToViperTranslator) {
  private val semanticAnalyser = translator.semanticAnalyser

  private def heapLocationAsField(typ: PType): vpr.Field =
    vpr.Field(s"$$h_$typ", translator.translateNonVoid(typ))()

  private def referencedType(id: PIdnUse): PType = {
    val entity = semanticAnalyser.entity(id).asInstanceOf[RegularEntity]
    val decl = entity.declaration.asInstanceOf[PTypedDeclaration]
    val typ = decl.typ.asInstanceOf[PRefType]

    typ.referencedType
  }

  def heapLocations(tree: VoilaTree): Vector[vpr.Field] = {
    tree.nodes.collect {
      case access: PHeapAccess => heapLocationAsField(referencedType(access.location))
    }.distinct
  }

  def translate(read: PHeapRead): vpr.Stmt = {
    val voilaType = referencedType(read.location)
    val viperType = translator.translateNonVoid(voilaType)

    val rcvr = vpr.LocalVar(read.location.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)
    val lv = vpr.LocalVar(read.lhs.name)(typ = viperType)

    vpr.LocalVarAssign(lv, vpr.FieldAccess(rcvr, fld)())()
  }

  def translate(write: PHeapWrite): vpr.Stmt = {
    val voilaType = referencedType(write.location)
    val viperType = translator.translateNonVoid(voilaType)

    val rcvr = vpr.LocalVar(write.location.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)

    vpr.FieldAssign(vpr.FieldAccess(rcvr, fld)(), translator.translate(write.rhs))()
  }
}