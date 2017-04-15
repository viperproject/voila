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

class PProgramToViperTranslator() extends Translator[PProgram, vpr.Program] {
  val returnVarName = "ret"
  val heapFieldName = "$h"

  def translate(program: PProgram): vpr.Program = {
    vpr.Program(
      domains = Nil,
      fields = Nil,
      functions = Nil,
      predicates = Nil,
      methods = program.procedures map translate)()
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
      _locals = Nil,
      _body = vpr.Seqn(procedure.body map translate)())()
  }

  def translate(statement: PStatement): vpr.Stmt = statement match {
    case PBlock(stmts) =>
      vpr.Seqn(stmts map translate)()
    case PIf(cond, thn, els) =>
      vpr.If(translate(cond), translate(thn), translate(els))()
    case PWhile(cond, body) =>
      vpr.While(translate(cond), Nil, Nil, translate(body))()
    case PAssign(id, rhs) =>
      /* TODO: Use correct type */
      vpr.LocalVarAssign(vpr.LocalVar(id.name)(typ = vpr.Int), translate(rhs))()
    case PHeapRead(id, lhs) =>
      /* TODO: Use correct type */
      val rcvr = vpr.LocalVar(id.name)(typ = vpr.Int)
      val fld = vpr.Field(heapFieldName, typ = vpr.Int)()
      val lv = vpr.LocalVar(lhs.name)(typ = vpr.Int)
      vpr.LocalVarAssign(lv, vpr.FieldAccess(rcvr, fld)())()
    case PHeapWrite(id, rhs) =>
      /* TODO: Use correct type */
      val rcvr = vpr.LocalVar(id.name)(typ = vpr.Int)
      val fld = vpr.Field(heapFieldName, typ = vpr.Int)()
      vpr.FieldAssign(vpr.FieldAccess(rcvr, fld)(), translate(rhs))()
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
    case PIdn(id) =>
      /* TODO: Use correct type */
      vpr.LocalVar(id.name)(typ = vpr.Int)
  }

  def translate(declaration: PVarDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translateNonVoid(declaration.typ))()

  def translateNonVoid(typ: PType): vpr.Type = typ match {
    case PIntType() => vpr.Int
    case PBoolType() => vpr.Bool
    case PVoidType() => sys.error("Cannot translate type 'void'")
  }
}
