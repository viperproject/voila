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

  val returnVarName = "ret"

  val heapAccessTranslator = new HeapAccessTranslatorComponent(this)

  def translate(tree: VoilaTree): vpr.Program = {
    val fields = heapAccessTranslator.heapLocations(tree)
    val methods = tree.root.procedures map translate

    vpr.Program(
      domains = Nil,
      fields = fields,
      functions = Nil,
      predicates = Nil,
      methods = methods)()
  }

  def translate(procedure: PProcedure): vpr.Method = {
    val formalReturns: Seq[vpr.LocalVarDecl] =
      procedure.typ match {
        case PVoidType() => Nil
        case other => Seq(vpr.LocalVarDecl(returnVarName, translateNonVoid(procedure.typ))())
      }

    vpr.Method(
      name = procedure.id.name,
      formalArgs = procedure.args map translate,
      formalReturns = formalReturns,
      _pres = Nil,
      _posts = Nil,
      _locals = procedure.locals map translate,
      _body = vpr.Seqn(procedure.body map translate)())()
  }

  def translate(declaration: PFormalArgumentDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translateNonVoid(declaration.typ))()

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
    case PFuncApp(id, args) =>
      /* TODO: Use correct type */
      /* TODO: Use correct formal args  */
      vpr.FuncApp(id.name, args map translate)(vpr.NoPosition, vpr.NoInfo, typ = vpr.Int, formalArgs = Nil, vpr.NoTrafos)
    case PIdnExp(id) =>
      /* TODO: Use correct type */
      vpr.LocalVar(id.name)(typ = vpr.Int)
  }

  def translate(declaration: PLocalVariableDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translateNonVoid(declaration.typ))()

  def translateNonVoid(typ: PType): vpr.Type = typ match {
    case PIntType() => vpr.Int
    case PBoolType() => vpr.Bool
    case PRefType(_) => vpr.Ref
    case unsupported@(_: PVoidType | _: PUnknownType) =>
      sys.error(s"Cannot translate type '$unsupported'")
  }
}

class HeapAccessTranslatorComponent(translator: PProgramToViperTranslator) {
  private val semanticAnalyser = translator.semanticAnalyser

  private def heapLocationAsField(typ: PType): vpr.Field =
    vpr.Field(s"$$h_$typ", translator.translateNonVoid(typ))()

  private def referencedType(id: PIdnUse): PType = {
    val entity = semanticAnalyser.entity(id).asInstanceOf[WelldefinedEntity]
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