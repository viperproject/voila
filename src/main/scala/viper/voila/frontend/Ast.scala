/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.output.PrettyExpression
import viper.silver
import viper.voila.VoilaGlobalState

/*
 * Top-level nodes
 */

sealed abstract class PAstNode extends Product {
  def pretty(prettyPrinter: PrettyPrinter = defaultPrettyPrinter): String =
    prettyPrinter.format(this)

  lazy val pretty: String = pretty()
  override lazy val toString: String = pretty

  def position: silver.ast.SourcePosition = {
    VoilaGlobalState.positions.getStart(this) match {
      case Some(position) => translate(position)
      case None => sys.error(s"Failed to find position for node ${this.getClass.getSimpleName}: $this")
    }
  }

  def lineColumnPosition: silver.ast.LineColumnPosition = {
    val pos = this.position

    silver.ast.LineColumnPosition(pos.line, pos.column)
  }
}

sealed trait PScope

case class PProgram(structs: Vector[PStruct],
                    regions: Vector[PRegion],
                    predicates: Vector[PPredicate],
                    procedures: Vector[PProcedure])
    extends PAstNode with PScope

/*
 * Modifiers
 */

sealed trait PModifier extends PAstNode

sealed trait PAtomicityModifier extends PModifier

case class PNonAtomic() extends PAtomicityModifier
case class PPrimitiveAtomic() extends PAtomicityModifier
case class PAbstractAtomic() extends PAtomicityModifier

sealed trait PGuardModifier extends PModifier

case class PUniqueGuard() extends PGuardModifier
case class PDuplicableGuard() extends PGuardModifier

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
case class PFormalReturnDecl(id: PIdnDef, typ: PType) extends PDeclaration
case class PLocalVariableDecl(id: PIdnDef, typ: PType) extends PDeclaration
case class PGuardDecl(id: PIdnDef, modifier: PGuardModifier) extends PDeclaration

case class PLogicalVariableBinder(id: PIdnDef) extends PDeclaration with PExpression

sealed trait PBindingContext extends PAstNode

/*
 * Specification clauses
 */

sealed trait PSpecificationClause extends PAstNode

case class PInterferenceClause(variable: PLogicalVariableBinder, set: PExpression, region: PIdnUse)
    extends PSpecificationClause with PBindingContext

case class PPreconditionClause(assertion: PExpression) extends PSpecificationClause
case class PPostconditionClause(assertion: PExpression) extends PSpecificationClause
case class PInvariantClause(assertion: PExpression) extends PSpecificationClause

/*
 * Actions
 */

sealed trait PAction extends PAstNode {
  def guard: PIdnUse
  def from: PExpression
  def to: PExpression
}

/* TODO: Try unifying the action nodes */

/* G: 0 ~> Set(0, 1) */
case class PAction1(guard: PIdnUse, from: PExpression, to: PExpression) extends PAction

/* G: ?n ~> Int */
case class PAction2(guard: PIdnUse, from: PLogicalVariableBinder, to: PExpression)
    extends PAction with PBindingContext with PScope

/* G: ?n if b(n) ~> Set(?m | c(n, m)) */
case class PAction3(guard: PIdnUse,
                    from: PLogicalVariableBinder,
                    constraint: PExpression,
                    to: PExpression)
    extends PAction with PBindingContext with PScope

/*
 * Members
 */

sealed trait PMember extends PDeclaration with PScope

case class PStruct(id: PIdnDef, fields: Vector[PFormalArgumentDecl]) extends PMember

case class PRegion(id: PIdnDef,
                   formalInArgs: Vector[PFormalArgumentDecl],
                   formalOutArgs: Vector[PFormalArgumentDecl],
                   guards: Vector[PGuardDecl],
                   interpretation: PExpression,
                   state: PExpression,
                   actions: Vector[PAction])
    extends PMember {

  val regionId: PFormalArgumentDecl = formalInArgs.head
}

case class PProcedure(id: PIdnDef,
                      formalArgs: Vector[PFormalArgumentDecl],
                      formalReturns: Vector[PFormalReturnDecl],
                      inters: Vector[PInterferenceClause],
                      pres: Vector[PPreconditionClause],
                      posts: Vector[PPostconditionClause],
                      locals: Vector[PLocalVariableDecl],
                      body: Option[PStatement],
                      atomicity: PAtomicityModifier)
    extends PMember with PDeclaration

case class PPredicate(id: PIdnDef,
                      formalArgs: Vector[PFormalArgumentDecl],
                      body: Option[PExpression])
    extends PMember

/*
 * Statements
 */

sealed trait PStatement extends PAstNode {
  def statementName: String
}

sealed trait PCompoundStatement extends PStatement {
  def components: Vector[PStatement]
}

case class PSkip() extends PStatement {
  val statementName = "skip"
}

case class PSeqComp(first: PStatement, second: PStatement) extends PCompoundStatement {
  val statementName = "seq-comp"
  val components: Vector[PStatement] = Vector(first, second)
}

case class PIf(cond: PExpression, thn: PStatement, els: Option[PStatement])
    extends PCompoundStatement {

  val statementName = "if-then-else"
  val components: Vector[PStatement] = Vector(thn) ++ els
}

case class PWhile(cond: PExpression, invariants: Vector[PInvariantClause], body: PStatement)
    extends PCompoundStatement {

  val statementName = "while"
  val components: Vector[PStatement] = Vector(body)
}

case class PAssign(lhs: PIdnUse, rhs: PExpression) extends PStatement {
  val statementName = "assign"
}

sealed trait PHeapAccess extends PStatement {
  def location: PLocation
}

case class PHeapWrite(location: PLocation, rhs: PExpression) extends PHeapAccess {
  val statementName = "heap-write"
}

case class PHeapRead(lhs: PIdnUse, location: PLocation) extends PHeapAccess {
  val statementName = "heap-read"
}

case class PProcedureCall(procedure: PIdnUse, arguments: Vector[PExpression], rhs: Vector[PIdnUse])
    extends PStatement {

  val statementName = s"call:${procedure.name}"
}

sealed trait PGhostStatement extends PStatement

sealed trait PFoldUnfold extends PAstNode{
  def predicateExp: PPredicateExp
}

case class PFold(predicateExp: PPredicateExp) extends PFoldUnfold with PGhostStatement {
  val statementName = "fold"
}

case class PUnfold(predicateExp: PPredicateExp) extends PFoldUnfold with PGhostStatement {
  val statementName = "unfold"
}

case class PInhale(assertion: PExpression) extends PGhostStatement { val statementName = "inhale" }
case class PExhale(assertion: PExpression) extends PGhostStatement { val statementName = "exhale" }
case class PAssume(assertion: PExpression) extends PGhostStatement { val statementName = "assume" }
case class PAssert(assertion: PExpression) extends PGhostStatement { val statementName = "assert" }
case class PHavocVariable(variable: PIdnUse) extends PGhostStatement { val statementName = "havoc" }
case class PHavocLocation(location: PLocation) extends PGhostStatement { val statementName = "havoc" }

case class PUseRegionInterpretation(regionPredicate: PPredicateExp) extends PGhostStatement {
  val statementName = "use-region-interpretation"
}

sealed trait PRuleStatement extends PStatement

case class PMakeAtomic(regionPredicate: PPredicateExp, guard: PGuardExp, body: PStatement)
    extends PRuleStatement with PCompoundStatement
{
  val statementName = "make-atomic"
  val components: Vector[PStatement] = Vector(body)
}

case class PUpdateRegion(regionPredicate: PPredicateExp, body: PStatement)
    extends PRuleStatement with PCompoundStatement
{
  val statementName = "update-region"
  val components: Vector[PStatement] = Vector(body)
}

case class PUseAtomic(regionPredicate: PPredicateExp, guard: PGuardExp, body: PStatement)
    extends PRuleStatement with PCompoundStatement
{
  val statementName = "use-atomic"
  val components: Vector[PStatement] = Vector(body)
}

case class POpenRegion(regionPredicate: PPredicateExp, body: PStatement)
    extends PRuleStatement with PCompoundStatement
{
  val statementName = "open-region"
  val components: Vector[PStatement] = Vector(body)
}

/*
 * Expressions
 */

sealed trait PExpression extends PAstNode with PrettyExpression

sealed trait PLiteral extends PExpression

case class PTrueLit() extends PLiteral
case class PFalseLit() extends PLiteral
case class PNullLit() extends PLiteral
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
case class PMul(left: PExpression, right: PExpression) extends PBinOp
case class PMod(left: PExpression, right: PExpression) extends PBinOp
case class PDiv(left: PExpression, right: PExpression) extends PBinOp

case class PIdnExp(id: PIdnUse) extends PExpression

case class PPredicateExp(predicate: PIdnUse, arguments: Vector[PExpression])
    extends PExpression with PBindingContext

case class PUnfolding(predicateExp: PPredicateExp, body: PExpression)
    extends PFoldUnfold with PExpression

/*
 * Collection expressions
 */

sealed trait PCollectionExp extends PExpression

sealed trait PExplicitCollection extends PCollectionExp with PLiteral {
  def elements: Vector[PExpression]
  def typeAnnotation: Option[PType]
}

sealed trait PSetExp extends PCollectionExp

case class PExplicitSet(elements: Vector[PExpression], typeAnnotation: Option[PType])
    extends PSetExp with PExplicitCollection

case class PSetComprehension(qvar: PLogicalVariableBinder,
                             filter: PExpression,
                             typeAnnotation: Option[PType])
    extends PSetExp with PLiteral with PBindingContext with PScope

case class PIntSet() extends PSetExp with PLiteral
case class PNatSet() extends PSetExp with PLiteral

case class PSetContains(element: PExpression, set: PExpression) extends PSetExp with PBinOp {
  val left: PExpression = element
  val right: PExpression = set
}

sealed trait PSeqExp extends PCollectionExp

case class PExplicitSeq(elements: Vector[PExpression], typeAnnotation: Option[PType])
    extends PSeqExp with PExplicitCollection

case class PSeqSize(seq: PExpression) extends PSeqExp
case class PSeqHead(seq: PExpression) extends PSeqExp
case class PSeqTail(seq: PExpression) extends PSeqExp

/*
 * Miscellaneous expressions
 */

case class PPointsTo(location: PLocation, value: PExpression)
    extends PExpression with PBindingContext

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
sealed trait PInternalType extends PType

case class PIntType() extends PType
case class PBoolType() extends PType
case class PRegionIdType() extends PType

case class PNullType() extends PInternalType
case class PUnknownType() extends PInternalType

case class PRefType(id: PIdnUse) extends PType

sealed trait PCollectionType extends PType {
  def elementType: PType
}

case class PSetType(elementType: PType) extends PCollectionType
case class PSeqType(elementType: PType) extends PCollectionType

/*
 * Miscellaneous
 */

case class PLocation(receiver: PIdnUse, field: PIdnUse) extends PAstNode
