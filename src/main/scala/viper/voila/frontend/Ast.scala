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

case class PFormalArgumentDecl(id: PIdnDef, typ: PType) extends PDeclaration
case class PLocalVariableDecl(id: PIdnDef, typ: PType) extends PDeclaration
case class PGuardDecl(id: PIdnDef, duplicable: Boolean) extends PDeclaration
case class PLogicalVariableDecl(id: PIdnDef) extends PDeclaration

/*
 * Specification clauses
 */

sealed trait PSpecificationClause extends PAstNode

case class PInterferenceClause(variable: PIdnUse, set: PExpression, regionId: PIdnUse)
    extends PSpecificationClause

case class PPreconditionClause(assertion: PExpression) extends PSpecificationClause
case class PPostconditionClause(assertion: PExpression) extends PSpecificationClause
case class PInvariantClause(assertion: PExpression) extends PSpecificationClause

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
                   actions: Vector[PAction])
    extends PMember


case class PAction(guard: PIdnUse, from: PExpression, to: PExpression) extends PAstNode

case class PProcedure(id: PIdnDef,
                      formalArgs: Vector[PFormalArgumentDecl],
                      typ: PType,
                      inters: Vector[PInterferenceClause],
                      pres: Vector[PPreconditionClause],
                      posts: Vector[PPostconditionClause],
                      locals: Vector[PLocalVariableDecl],
                      body: Option[Vector[PStatement]],
                      isPrimitiveAtomic: Boolean)
    extends PMember with PDeclaration

case class PPredicate(id: PIdnDef,
                      formalArgs: Vector[PFormalArgumentDecl],
                      body: PExpression)
    extends PMember

/*
 * Statements
 */

sealed trait PStatement extends PAstNode {
  def statementName: String
}

case class PSkip() extends PStatement {
  val statementName = "skip"
}

case class PBlock(stmts: Vector[PStatement]) extends PStatement {
  val statementName = "seq-comp"
}

case class PIf(cond: PExpression, thn: PStatement, els: Option[PStatement]) extends PStatement {
  val statementName = "if-then-else"
}

case class PWhile(cond: PExpression, invariants: Vector[PInvariantClause], body: Vector[PStatement])
    extends PStatement {

  val statementName = "while"
}

case class PAssign(lhs: PIdnUse, rhs: PExpression) extends PStatement {
  val statementName = "assign"
}

sealed trait PHeapAccess extends PStatement {
  def location: PIdnUse
}

case class PHeapWrite(location: PIdnUse, rhs: PExpression) extends PHeapAccess {
  val statementName = "heap-write"
}

case class PHeapRead(lhs: PIdnUse, location: PIdnUse) extends PHeapAccess {
  val statementName = "heap-read"
}

case class PProcedureCall(procedure: PIdnUse, arguments: Vector[PExpression], rhs: Option[PIdnUse])
    extends PStatement {

  val statementName = s"call:${procedure.name}"
}

sealed trait PGhostStatement extends PStatement

case class PFold(predicate: PIdnUse, arguments: Vector[PExpression])
    extends PGhostStatement with PPredicateAccess
{
  val statementName = "fold"
}

case class PUnfold(predicate: PIdnUse, arguments: Vector[PExpression])
    extends PGhostStatement with PPredicateAccess
{
  val statementName = "unfold"
}

case class PInhale(assertion: PExpression) extends PGhostStatement { val statementName = "inhale" }
case class PExhale(assertion: PExpression) extends PGhostStatement { val statementName = "exhale" }

sealed trait PRuleStatement extends PStatement

case class PMakeAtomic(regionPredicate: PPredicateExp, guard: PGuardExp, body: Vector[PStatement])
    extends PRuleStatement
{
  val statementName = "make-atomic"
}

case class PUpdateRegion(regionPredicate: PPredicateExp, body: Vector[PStatement])
    extends PRuleStatement
{
  val statementName = "update-region"
}

/*
 * Expressions
 */

sealed trait PExpression extends PAstNode with PrettyExpression

sealed trait PLiteral extends PExpression

case class PTrueLit() extends PLiteral
case class PFalseLit() extends PLiteral
case class PIntLit(value: BigInt) extends PLiteral

case class PRet() extends PLiteral

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

case class PPredicateExp(predicate: PIdnUse, arguments: Vector[PExpression])
    extends PExpression with PPredicateAccess

sealed trait PSetExp extends PExpression

case class PExplicitSet(args: Vector[PExpression]) extends PSetExp with PLiteral
case class PIntSet() extends PSetExp with PLiteral
case class PNatSet() extends PSetExp with PLiteral

case class PPointsTo(id: PIdnUse, value: Either[PLogicalVariableDecl, PExpression])
    extends PExpression

case class PGuardExp(guard: PIdnUse, regionId: PIdnUse) extends PExpression

sealed trait PTrackingResource extends PExpression {
  def regionId: PIdnUse
}

case class PDiamond(regionId: PIdnUse) extends PTrackingResource

case class PRegionUpdateWitness(regionId: PIdnUse, from: PExpression, to: PExpression)
    extends PTrackingResource

case class PIrrelevantValue() extends PExpression

/*
 * Types
 */

sealed trait PType extends PAstNode

case class PIntType() extends PType { override def toString = "int" }
case class PBoolType() extends PType { override def toString = "bool" }
case class PSetType(elementType: PType) extends PType { override def toString = "set" }

case class PRefType(referencedType: PType) extends PType {
  override def toString = s"$referencedType*"
}

case class PRegionIdType() extends PType { override def toString = "id" }
case class PVoidType() extends PType { override def toString = "void" }

case class PUnknownType() extends PType { override def toString = "<unknown>" }

/*
 * Miscellaneous
 */

sealed trait PPredicateAccess extends PAstNode {
  def predicate: PIdnUse
  def arguments: Vector[PExpression]
}

object PPredicateAccess {
  def unapply(acc: PPredicateAccess): Option[(PIdnUse, Vector[PExpression])] =
    Some((acc.predicate, acc.arguments))
}
