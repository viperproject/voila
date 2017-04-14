/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.output.PrettyExpression

sealed abstract class PAstNode extends Product

case class PProgram(procedures: Vector[PProcedure]) extends PAstNode

/*
 * Identifiers
 */

trait PIdnNode extends PAstNode {
  def id: String
}

case class PIdnDef(id: String) extends PIdnNode
case class PIdnUse(id: String) extends PIdnNode

/*
 * Declarations
 */

trait PDeclaration extends PAstNode {
  def name: PIdnDef
}

case class PVarDecl(name: PIdnDef, typ: PType) extends PDeclaration

/*
 * Members
 */

case class PProcedure(name: PIdnDef,
                      args: Vector[PVarDecl],
                      typ: PType,
                      body: Vector[PStatement])
    extends PDeclaration

/*
 * Statements
 */

trait PStatement extends PAstNode

case class PBlock(stmts: Vector[PStatement]) extends PStatement
case class PIf(cond: PExpression, thn: PStatement, els: PStatement) extends PStatement
case class PWhile(cond: PExpression, body: PStatement) extends PStatement
case class PAssign(name: PIdnUse, rhs: PExpression) extends PStatement
case class PHeapRead(name: PIdnUse, lhs: PIdnUse) extends PStatement
case class PHeapWrite(name: PIdnUse, rhs: PExpression) extends PStatement

/*
 *
 */

trait PExpression extends PAstNode with PrettyExpression

trait PLiteral extends PExpression

case class PTrueLit() extends PLiteral
case class PFalseLit() extends PLiteral
case class PIntLit(value: BigInt) extends PLiteral

trait PUnOp extends PExpression {
  def operand: PExpression
}

trait PBinOp extends PExpression {
  def left: PExpression
  def right: PExpression
}

case class PEquals(left: PExpression, right: PExpression) extends PExpression

case class PAnd(left: PExpression, right: PExpression) extends PExpression
case class POr(left: PExpression, right: PExpression) extends PExpression
case class PConditional(cond: PExpression, thn: PExpression, els: PExpression) extends PExpression
case class PNot(operand: PExpression) extends PUnOp

case class PAdd(left: PExpression, right: PExpression) extends PExpression
case class PSub(left: PExpression, right: PExpression) extends PExpression

case class PUnaryMinus(operand: PExpression) extends PUnOp
case class PUnaryPlus(operand: PExpression) extends PUnOp

case class PIdn(name: PIdnUse) extends PExpression

trait PApp extends PExpression {
  def callee: PExpression
  def args: Vector[PExpression]
}

case class PFuncApp(callee: PExpression, args: Vector[PExpression]) extends PApp

/*
 * Types
 */

trait PType extends PAstNode

case class PVoidType() extends PType {
  override def toString = "void"
}

case class PIntType() extends PType {
  override def toString = "int"
}

case class PBoolType() extends PType {
  override def toString = "bool"
}