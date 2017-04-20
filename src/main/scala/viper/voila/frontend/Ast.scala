/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.output.PrettyExpression

/*
 * Top-level nodes
 */

sealed abstract class PAstNode extends Product

case class PProgram(regions: Vector[PRegion],
                    predicates: Vector[PPredicate],
                    procedures: Vector[PProcedure])
    extends PAstNode

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

sealed trait PTypedDeclaration extends PDeclaration {
  def typ: PType
}

case class PFormalArgumentDecl(id: PIdnDef, typ: PType) extends PTypedDeclaration
case class PLocalVariableDecl(id: PIdnDef, typ: PType) extends PTypedDeclaration
case class PGuardDecl(id: PIdnDef, duplicable: Boolean) extends PDeclaration
case class PLogicalVariableDecl(id: PIdnDef) extends PDeclaration with PExpression

/*
 * Members
 */

sealed trait PMember extends PDeclaration

case class PRegion(id: PIdnDef,
                   regionId: PFormalArgumentDecl,
                   formalArgs: Vector[PFormalArgumentDecl],
                   guards: Vector[PGuardDecl],
                   interpretation: PExpression,
                   state: PExpression,
                   action: Vector[PAction])
    extends PMember


case class PAction(guard: PIdnUse, from: PExpression, to: PExpression) extends PAstNode

case class PProcedure(id: PIdnDef,
                      formalArgs: Vector[PFormalArgumentDecl],
                      typ: PType,
                      pres: Vector[PExpression],
                      posts: Vector[PExpression],
                      inters: Vector[PInterferenceClause],
                      locals: Vector[PLocalVariableDecl],
                      body: Vector[PStatement])
    extends PMember with PTypedDeclaration

case class PInterferenceClause(variable: PIdnUse, set: PExpression, regionId: PIdnUse)
    extends PAstNode

case class PPredicate(id: PIdnDef,
                      formalArgs: Vector[PFormalArgumentDecl],
                      body: PExpression)
    extends PMember

/*
 * Statements
 */

sealed trait PStatement extends PAstNode

case class PBlock(stmts: Vector[PStatement]) extends PStatement
case class PIf(cond: PExpression, thn: PStatement, els: PStatement) extends PStatement
case class PWhile(cond: PExpression, body: PStatement) extends PStatement
case class PAssign(lhs: PIdnUse, rhs: PExpression) extends PStatement

sealed trait PHeapAccess extends PStatement {
  def location: PIdnUse
}

case class PHeapWrite(location: PIdnUse, rhs: PExpression) extends PHeapAccess
case class PHeapRead(lhs: PIdnUse, location: PIdnUse) extends PHeapAccess

/*
 * Expressions
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

case class PIdnExp(id: PIdnUse) extends PExpression
case class PCallExp(id: PIdnUse, args: Vector[PExpression]) extends PExpression with PCall

sealed trait PSetExp extends PExpression

case class PExplicitSet(args: Vector[PExpression]) extends PSetExp with PLiteral
case class PIntSet() extends PSetExp with PLiteral
case class PNatSet() extends PSetExp with PLiteral

case class PPointsTo(id: PIdnUse, value: PExpression) extends PExpression

/*
 * Types
 */

sealed trait PType extends PAstNode

case class PIntType() extends PType { override def toString = "int" }
case class PBoolType() extends PType { override def toString = "bool" }
case class PSetType() extends PType { override def toString = "bool" }

case class PRefType(referencedType: PType) extends PType {
  override def toString = s"$referencedType*"
}

case class PRegionIdType() extends PType { override def toString = "id" }
case class PVoidType() extends PType { override def toString = "void" }

case class PUnknownType() extends PType { override def toString = "<unknown>" }

/*
 * Miscellaneous
 */

sealed trait PCall extends PAstNode {
  def id: PIdnUse
  def args: Vector[PExpression]
}

object PCall {
  def unapply(call: PCall): Option[(PIdnUse, Vector[PExpression])] =
    Some((call.id, call.args))
}
