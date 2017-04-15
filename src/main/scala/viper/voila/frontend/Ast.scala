/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import java.lang.reflect.Constructor
import org.bitbucket.inkytonik.kiama.output.PrettyExpression
import viper.silver.ast.utility.Rewriter.Rewritable

sealed abstract class PAstNode extends Rewritable {
  private val constructor: Constructor[_] = this.getClass.getConstructors.head

  def duplicate(children: Seq[AnyRef]): Rewritable = {
    constructor.newInstance(children).asInstanceOf[Rewritable]
  }
}

case class PProgram(procedures: Vector[PProcedure]) extends PAstNode

/*
 * Identifiers
 */

sealed trait PIdnNode extends PAstNode {
  def name: String
}

case class PIdnDef(name: String) extends PIdnNode
case class PIdnUse(name: String) extends PIdnNode

/*
 * Declarations
 */

sealed trait PDeclaration extends PAstNode {
  def id: PIdnDef
}

case class PVarDecl(id: PIdnDef, typ: PType) extends PDeclaration

/*
 * Members
 */

case class PProcedure(id: PIdnDef,
                      args: Vector[PVarDecl],
                      typ: PType,
                      body: Vector[PStatement])
    extends PDeclaration

/*
 * Statements
 */

sealed trait PStatement extends PAstNode

case class PBlock(stmts: Vector[PStatement]) extends PStatement
case class PIf(cond: PExpression, thn: PStatement, els: PStatement) extends PStatement
case class PWhile(cond: PExpression, body: PStatement) extends PStatement
case class PAssign(id: PIdnUse, rhs: PExpression) extends PStatement
case class PHeapRead(id: PIdnUse, lhs: PIdnUse) extends PStatement
case class PHeapWrite(id: PIdnUse, rhs: PExpression) extends PStatement

/*
 *
 */

sealed trait PExpression extends PAstNode with PrettyExpression

sealed trait PLiteral extends PExpression

case class PTrueLit() extends PLiteral
case class PFalseLit() extends PLiteral
case class PIntLit(value: BigInt) extends PLiteral

sealed trait PUnOp extends PExpression {
  def operand: PExpression
}

sealed trait PBinOp extends PExpression {
  def left: PExpression
  def right: PExpression
}

case class PEquals(left: PExpression, right: PExpression) extends PBinOp

case class PAnd(left: PExpression, right: PExpression) extends PBinOp
case class POr(left: PExpression, right: PExpression) extends PBinOp
case class PConditional(cond: PExpression, thn: PExpression, els: PExpression) extends PExpression
case class PNot(operand: PExpression) extends PUnOp

case class PLess(left: PExpression, right: PExpression) extends PBinOp
case class PAtMost(left: PExpression, right: PExpression) extends PBinOp
case class PGreater(left: PExpression, right: PExpression) extends PBinOp
case class PAtLeast(left: PExpression, right: PExpression) extends PBinOp

case class PAdd(left: PExpression, right: PExpression) extends PBinOp
case class PSub(left: PExpression, right: PExpression) extends PBinOp
//case class PUnaryMinus(operand: PExpression) extends PUnOp
//case class PUnaryPlus(operand: PExpression) extends PUnOp

case class PIdn(name: PIdnUse) extends PExpression

sealed trait PApp extends PExpression {
  def id: PIdnUse
  def args: Vector[PExpression]
}

case class PFuncApp(id: PIdnUse, args: Vector[PExpression]) extends PApp

/*
 * Types
 */

sealed trait PType extends PAstNode

case class PVoidType() extends PType {
  override def toString = "void"
}

case class PIntType() extends PType {
  override def toString = "int"
}

case class PBoolType() extends PType {
  override def toString = "bool"
}