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

  lazy val source: Option[String] = {
    if (VoilaGlobalState.positions == null) None
    else VoilaGlobalState.positions.textOf(this)
  }

  lazy val formatForUsers: String = source.getOrElse(pretty)
  lazy val formatForDevelopers: String = pretty

  override lazy val toString: String = formatForDevelopers

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
case class PDivisibleGuard() extends PGuardModifier

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

sealed trait PVariableDeclaration extends PTypedDeclaration

case class PFormalArgumentDecl(id: PIdnDef, typ: PType) extends PVariableDeclaration
case class PFormalReturnDecl(id: PIdnDef, typ: PType) extends PVariableDeclaration
case class PLocalVariableDecl(id: PIdnDef, typ: PType) extends PVariableDeclaration

case class PGuardDecl(id: PIdnDef,
                      formalArguments: Vector[PFormalArgumentDecl],
                      modifier: PGuardModifier)
  extends PDeclaration with PScope

sealed trait PLogicalVariableBinder extends PExpression

case class PNamedBinder(id: PIdnDef, typeAnnotation: Option[PType])
    extends PLogicalVariableBinder with PDeclaration

case class PAnonymousBinder() extends PLogicalVariableBinder

sealed trait PBindingContext extends PAstNode

/*
 * Specification clauses
 */

sealed trait PSpecificationClause extends PAstNode

case class PInterferenceClause(variable: PNamedBinder, set: PExpression, region: Option[PIdnUse])
    extends PSpecificationClause with PBindingContext

sealed trait PAssertionClause extends PSpecificationClause {
  def assertion: PExpression
}

case class PPreconditionClause(assertion: PExpression) extends PAssertionClause
case class PPostconditionClause(assertion: PExpression) extends PAssertionClause
case class PInvariantClause(assertion: PExpression) extends PAssertionClause

/*
 * Actions
 */

case class PAction(binders: Vector[PNamedBinder], condition: PExpression, guards: Vector[PBaseGuardExp], from: PExpression, to: PExpression)
    extends PAstNode with PBindingContext with PScope {

  def binds(binder: PLogicalVariableBinder): Boolean =
    binder.isInstanceOf[PNamedBinder] && binders.exists(_ eq binder)
}

/*
 * Members
 */

sealed trait PMember extends PDeclaration with PScope

sealed trait PMemberWithFields extends PMember {
  def fields: Vector[PFormalArgumentDecl] // TODO: Introduce PFieldDecl; use instead of PFormalArgumentDecl
}

case class PStruct(id: PIdnDef, fields: Vector[PFormalArgumentDecl]) extends PMemberWithFields

case class PRegion(id: PIdnDef,
                   formalInArgs: Vector[PFormalArgumentDecl],
                   formalOutArgs: Vector[PFormalArgumentDecl],
                   guards: Vector[PGuardDecl],
                   interpretation: PExpression,
                   state: PExpression,
                   actions: Vector[PAction],
                   fields: Vector[PFormalArgumentDecl] = Vector.empty)
    extends PMemberWithFields {

  val regionId: PFormalArgumentDecl = formalInArgs.head

  val explicitArgumentCount: Int = formalInArgs.length + formalOutArgs.length
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

sealed trait PMacro extends PMember {
  type Body <: PAstNode

  def id: PIdnDef
  def body: Body
}

case class PTypeMacro(id: PIdnDef,
                      formalArguments: Option[Vector[PIdnDef]],
                      body: PType)
    extends PMacro {

  type Body = PType
}

case class PExpressionMacro(id: PIdnDef,
                            formalArguments: Option[Vector[PIdnDef]],
                            body: PExpression)
    extends PMacro {

  type Body = PExpression
}

case class PStatementMacro(id: PIdnDef,
                           formalArguments: Vector[PIdnDef],
                           locals: Vector[PLocalVariableDecl],
                           body: PStatement)
    extends PMacro {

  type Body = PStatement
}

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

case class PNewStmt(lhs: PIdnUse,
                    constructor: PIdnUse,
                    arguments: Vector[PExpression],
                    guards: Option[Vector[PBaseGuardExp]],
                    initializer: Option[PStatement])
    extends PStatement {

  val statementName = s"new:${constructor.name}"
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
case class PLemmaApplication(call: PProcedureCall) extends PGhostStatement { val statementName = "apply" }

case class PUseRegionInterpretation(regionPredicate: PPredicateExp) extends PGhostStatement {
  val statementName = "use-region-interpretation"
}

case class PUseGuardUniqueness(guard: PRegionedGuardExp) extends PGhostStatement {
  val statementName = "use-guard-uniqueness"
}

sealed trait PRuleStatement extends PStatement {
  def body: PStatement
}

case class PMakeAtomic(regionPredicate: PPredicateExp, guards: Vector[PRegionedGuardExp], body: PStatement)
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

case class PUseAtomic(regionPredicate: PPredicateExp, guards: Vector[PRegionedGuardExp], body: PStatement)
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
case class PFracLiteral(numerator: BigInt, denominator: BigInt) extends PLiteral
case class PFullPerm() extends PLiteral
case class PNoPerm() extends PLiteral

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
case class PFrac(left: PExpression, right: PExpression) extends PBinOp
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

case class PSetComprehension(qvar: PNamedBinder,
                             filter: PExpression,
                             typeAnnotation: Option[PType])
    extends PSetExp with PLiteral with PBindingContext with PScope

case class PIntSet() extends PSetExp with PLiteral
case class PNatSet() extends PSetExp with PLiteral

case class PSetContains(element: PExpression, set: PExpression) extends PSetExp with PBinOp {
  val left: PExpression = element
  val right: PExpression = set
}

case class PSetSubset(left: PExpression, right: PExpression) extends PSetExp with PBinOp

case class PSetUnion(left: PExpression, right: PExpression) extends PSetExp with PBinOp

sealed trait PSeqExp extends PCollectionExp

case class PExplicitSeq(elements: Vector[PExpression], typeAnnotation: Option[PType])
    extends PSeqExp with PExplicitCollection

case class PSeqSize(seq: PExpression) extends PSeqExp
case class PSeqHead(seq: PExpression) extends PSeqExp
case class PSeqTail(seq: PExpression) extends PSeqExp


sealed trait PTupleExp extends PExpression

case class PExplicitTuple(elements: Vector[PExpression],
                          typeAnnotation: Option[Vector[PType]])
    extends PTupleExp

case class PTupleGet(tuple: PExpression, index: Int)
    extends PTupleExp with PUnOp {
      val operand: PExpression = tuple
    }

sealed trait PMapExp extends PExpression

case class PExplicitMap(elements: Vector[(PExpression, PExpression)],
                        typeAnnotation: Option[(PType, PType)])
    extends PMapExp

case class PMapUnion(left: PExpression, right: PExpression) extends PMapExp with PBinOp
case class PMapDisjoint(left: PExpression, right: PExpression) extends PMapExp with PBinOp
case class PMapUpdate(map: PExpression, key: PExpression, value: PExpression) extends PMapExp
case class PMapKeys(map: PExpression) extends PMapExp
case class PMapValues(map: PExpression) extends PMapExp
case class PMapContains(map: PExpression, key: PExpression) extends PMapExp
case class PMapLookup(map: PExpression, key: PExpression) extends PMapExp

/*
 * Miscellaneous expressions
 */

case class PPointsTo(location: PLocation, value: PExpression)
    extends PExpression with PBindingContext


sealed trait PGuardExp extends PExpression {
  def guard: PIdnUse
  def argument: PGuardArg
}

case class PBaseGuardExp(guard: PIdnUse, argument: PGuardArg) extends PGuardExp

case class PRegionedGuardExp(guard: PIdnUse, regionId: PIdnExp, argument: PGuardArg) extends PGuardExp


sealed trait PGuardArg extends PAstNode with PrettyExpression

case class PStandartGuardArg(arguments: Vector[PExpression]) extends PGuardArg

case class PSetGuardArg(set: PExpression) extends PGuardArg


sealed trait PTrackingResource extends PExpression {
  def regionId: PIdnUse
}

case class PDiamond(regionId: PIdnUse) extends PTrackingResource

case class PRegionUpdateWitness(regionId: PIdnUse, from: PExpression, to: PExpression)
    extends PTrackingResource

/*
 * Types
 */

sealed trait PType extends PAstNode
sealed trait PInternalType extends PType

case class PIntType() extends PType
case class PBoolType() extends PType
case class PRegionIdType() extends PType
case class PFracType() extends PType

case class PNullType() extends PInternalType
case class PUnknownType() extends PInternalType

case class PRefType(id: PIdnUse) extends PType

/* TODO: Is it worth having PCollectionType, given that pairs and maps don't extend it? Can this be changed? */

sealed trait PCollectionType extends PType {
  def elementType: PType
}

case class PSetType(elementType: PType) extends PCollectionType
case class PSeqType(elementType: PType) extends PCollectionType
case class PTupleType(elementTypes: Vector[PType]) extends PType
case class PMapType(keyType: PType, valueType: PType) extends PType

/*
 * Miscellaneous
 */

case class PLocation(receiver: PIdnUse, field: PIdnUse) extends PAstNode
