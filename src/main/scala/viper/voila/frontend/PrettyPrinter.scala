/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama

trait PrettyPrinter {
  def format(node: PAstNode): String
}

class DefaultPrettyPrinter extends PrettyPrinter with kiama.output.PrettyPrinter {
  override val defaultIndent = 2
  override val defaultWidth = 80

  def format(node: PAstNode): String =
    pretty(toDoc(node)).layout

  def toDoc(node: PAstNode): Doc =
    node match {
      case program: PProgram => toDoc(program)
      case declaration: PDeclaration => toDoc(declaration)
      case statement: PStatement => toDoc(statement)
      case expression: PExpression => toDoc(expression)
      case typ: PType => toDoc(typ)
      case _: PPredicateAccess => ???
      case modifier: PModifier => toDoc(modifier)
      case id: PIdnNode => toDoc(id)
      case clause: PSpecificationClause => toDoc(clause)
      case action: PAction => toDoc(action)
      case location: PLocation => toDoc(location)
    }

  def toDoc(action: PAction): Doc =
    action match {
      case PAction1(guard, from, to) =>
        toDoc(guard) <> ":" <+> toDoc(from) <+> "~>" <+> toDoc(to)
      case PAction2(guard, from, to) =>
        toDoc(guard) <> ":" <+> toDoc(from) <+> "~>" <+> toDoc(to)
      case PAction3(guard, qvar, constraint, to) =>
        toDoc(guard) <> ":" <+> toDoc(qvar) <+> "if" <+> toDoc(constraint) <+> "~>" <+> toDoc(to)
    }

  def toDoc(clause: PSpecificationClause): Doc = {
    clause match {
      case PPreconditionClause(assertion) => "requires" <+> toDoc(assertion)
      case PPostconditionClause(assertion) => "ensures" <+> toDoc(assertion)
      case PInvariantClause(assertion) => "invariant" <+> toDoc(assertion)

      case PInterferenceClause(variable, set, region) =>
        (  "interference" <+> toDoc(variable)
         <+> "in" <+> toDoc(set)
         <+> "on" <+> toDoc(region))
    }
  }

  def toDoc(modifier: PModifier): Doc = {
    modifier match {
      case modifier: PAtomicityModifier => toDoc(modifier)
      case modifier: PGuardModifier => toDoc(modifier)
    }
  }

  def toDoc(modifier: PAtomicityModifier): Doc = {
    modifier match {
      case PNotAtomic() => emptyDoc
      case PPrimitiveAtomic() => "primitive_atomic"
      case PAbstractAtomic() => "abstract_atomic"
    }
  }

  def toDoc(modifier: PGuardModifier): Doc = {
    modifier match {
      case PUniqueGuard() => "unique"
      case PDuplicableGuard() => "duplicable"
    }
  }

  def toDoc(id: PIdnNode): Doc = {
    id match {
      case PIdnDef(name) => name
      case PIdnUse(name) => name
    }
  }

  def toDoc(location: PLocation): Doc = {
    toDoc(location.receiver) <> "." <> toDoc(location.field)
  }

  def toDoc(program: PProgram): Doc = {
    val PProgram(structs, regions, predicates, procedures) = program

    (    ssep(structs map toDoc, line)
      <> line
      <> ssep(regions map toDoc, line)
      <> line
      <> ssep(predicates map toDoc, line)
      <> line
      <> ssep(procedures map toDoc, line))
  }

  def toDoc(declaration: PDeclaration): Doc = {
    declaration match {
      case member: PMember => toDoc(member)

      case PFormalArgumentDecl(id, typ) => toDoc(id) <> ":" <+> toDoc(typ)
      case PLocalVariableDecl(id, typ) =>  toDoc(typ) <+> toDoc(id)
      case PGuardDecl(id, modifier) =>  toDoc(modifier) <+> toDoc(id)
      case PLogicalVariableBinder(id) =>  "?" <> toDoc(id)
    }
  }

  def toDoc(declaration: PLogicalVariableBinder): Doc =
    toDoc(declaration: PDeclaration)

  def toDoc(member: PMember): Doc = {
    member match {
      case PStruct(id, fields) =>
        "struct" <+> toDoc(id) <>
        nest(braces(ssep(fields map toDoc, semi <> line)))

      case PRegion(id, regionId, formalArgs, guards, interpretation, state, actions) =>
        (   "region" <+> toDoc(id) <> asFormalArguments(formalArgs)
         <> nest("guards" <+> braces(ssep(guards map toDoc, semi <> line)))
         <> nest("interpretation" <+> braces(toDoc(interpretation)))
         <> nest("state" <+> braces(toDoc(state)))
         <> nest("actions" <+> braces(ssep(actions map toDoc, semi <> line))))

      case PProcedure(id, formalArgs, typ, inters, pres, posts, locals, optBody, atomicity) =>
        (   toDoc(atomicity) <+> toDoc(typ) <+> toDoc(id) <+> asFormalArguments(formalArgs) <> line
         <> nest(ssep(inters map toDoc, semi <> line)) <> line
         <> nest(ssep(pres map toDoc, semi <> line)) <> line
         <> (optBody match {
              case None =>
                require(locals.isEmpty)
                emptyDoc
              case Some(body) =>
                braces(ssep(locals map toDoc, semi <> line <> toDoc(body)))
            }))

      case PPredicate(id, formalArgs, optBody) =>
        (    "predicate" <+> toDoc(id) <> asFormalArguments(formalArgs)
         <+> (optBody match {
                case None => emptyDoc
                case Some(body) => braces(nest(toDoc(body)))
              }))
    }
  }

  def toDoc(procedure: PProcedure): Doc = {
    val PProcedure(id, formalArgs, typ, inters, pres, posts, locals, body, atomicity) = procedure

    val signatureDoc =
      toDoc(typ) <+> toDoc(id) <> asFormalArguments(formalArgs)

    val contractDoc = emptyDoc // TODO: Implement

    val bodyDoc = (
         ssep(locals map toDoc, line)
      <> line
      <> body.fold(emptyDoc)(toDoc)) // TODO: Account for abstract procedures

    signatureDoc <> nest(line <> contractDoc) <> braces(nest(line <> bodyDoc))
  }

  def toDoc(statement: PStatement): Doc =
    statement match {
      case rule: PRuleStatement => toDoc(rule)
      case ghost: PGhostStatement => toDoc(ghost)
      case PSeqComp(first, second) => toDoc(first) <> semi <> line <> toDoc(second)
      case PSkip() => "skip" <> semi
      case PAssign(lhs, rhs) => toDoc(lhs) <+> ":=" <+> toDoc(rhs)
      case PHeapRead(lhs, location) => toDoc(lhs) <+> ":=" <+> toDoc(location)
      case PHeapWrite(location, rhs) => toDoc(location) <+> ":=" <+> toDoc(rhs)

      case PIf(cond, thn, els) => ???

      case PWhile(cond, invariants, body) =>
        (   "while" <> parens(toDoc(cond)) <> line
         <> nest(ssep(invariants map toDoc, semi <> line)) <> line
         <> braces(nest(toDoc(body))))

      case PProcedureCall(procedure, arguments, optRhs) =>
        val lhsDoc = toDoc(procedure) <> asArguments(arguments)

        optRhs match {
          case Some(rhs) => toDoc(rhs) <+> ":=" <+> lhsDoc
          case None => lhsDoc
        }
    }

  def toDoc(statement: PGhostStatement): Doc = {
    statement match {
      case PFold(predicate, arguments) => "fold" <+> toDoc(predicate) <> asArguments(arguments)
      case PUnfold(predicate, arguments) => "unfold" <+> toDoc(predicate) <> asArguments(arguments)
      case PInhale(assertion) => "inhale" <+> toDoc(assertion)
      case PExhale(assertion) => "exhale" <+> toDoc(assertion)
      case PAssume(assertion) => "assume" <+> toDoc(assertion)
      case PAssert(assertion) => "assert" <+> toDoc(assertion)
      case PHavoc(variable) => "havoc" <+> toDoc(variable)
    }
  }

  def asArguments(arguments: Vector[PExpression]): Doc =
    parens(ssep(arguments map toDoc, comma <> space))

  def asFormalArguments(arguments: Vector[PFormalArgumentDecl]): Doc =
    parens(ssep(arguments map toDoc, comma <> space))

  def toDoc(rule: PRuleStatement): Doc = {
    rule match {
      case PMakeAtomic(regionPredicate, guard, body) =>
        (   "make_atomic" <> line
         <> nest("using" <+> toDoc(regionPredicate) <+> "with" <+> toDoc(guard) <> semi) <> line
         <> braces(nest(toDoc(body))))
      case PUseAtomic(regionPredicate, guard, body) =>
        (   "use_atomic" <> line
         <> nest("using" <+> toDoc(regionPredicate) <+> "with" <+> toDoc(guard) <> semi) <> line
         <> braces(nest(toDoc(body))))
      case PUpdateRegion(regionPredicate, body) =>
        (   "update_region" <> line
         <> nest("using" <+> toDoc(regionPredicate) <> semi) <> line
         <> braces(nest(toDoc(body))))
      case POpenRegion(regionPredicate, body) =>
        (   "open_region" <> line
         <> nest("using" <+> toDoc(regionPredicate) <> semi) <> line
         <> braces(nest(toDoc(body))))
    }
  }

  def toDoc(expression: PExpression): Doc =
    expression match {
      case PLogicalVariableBinder(id) => "?" <> toDoc(id)

      case PTrueLit() => "true"
      case PFalseLit() => "false"
      case PIntLit(value) => value.toString
      case PRet() => "ret"

      case PUnfolding(predicate, body) =>
        "unfolding" <+> toDoc(predicate) <+> "in" <+> toDoc(body)

      case PExplicitSet(args, typeAnnotation) =>
        "Set" <>
        typeAnnotation.fold(emptyDoc)(typ => "[" <> toDoc(typ) <> "]") <>
        "(" <> ssep(args map toDoc, comma <> space) <> ")"

      case PSetComprehension(qvar, filter, typeAnnotation) =>
        "Set" <>
        typeAnnotation.fold(emptyDoc)(typ => "[" <> toDoc(typ) <> "]") <>
        "(" <> toDoc(qvar) <+> "|" <+> toDoc(filter) <> ")"

      case PIntSet() => "Int"
      case PNatSet() => "Nat"

      case PNot(operand) => "!" <> toDoc(operand)

      /* TODO: Use associativity and precedence to avoid unncessary parentheses */
      case PEquals(left, right) => parens(toDoc(left) <+> "==" <+> toDoc(right))
      case PAnd(left, right) => parens(toDoc(left) <+> "&&" <+> toDoc(right))
      case POr(left, right) => parens(toDoc(left) <+> "||" <+> toDoc(right))
      case PLess(left, right) => parens(toDoc(left) <+> "<" <+> toDoc(right))
      case PAtMost(left, right) => parens(toDoc(left) <+> "<=" <+> toDoc(right))
      case PGreater(left, right) => parens(toDoc(left) <+> ">" <+> toDoc(right))
      case PAtLeast(left, right) => parens(toDoc(left) <+> ">=" <+> toDoc(right))
      case PAdd(left, right) => parens(toDoc(left) <+> "+" <+> toDoc(right))
      case PSub(left, right) => parens(toDoc(left) <+> "-" <+> toDoc(right))
      case PSetContains(element, set) => parens(toDoc(element) <+> "in" <+> toDoc(set))
      case PConditional(cond, thn, els) =>
        parens(toDoc(cond) <+> "?" <+> toDoc(thn) <+> ":" <+> toDoc(els))

      case PIdnExp(id) => toDoc(id)
      case PPredicateExp(predicate, arguments) =>
        toDoc(predicate) <> "(" <> ssep(arguments map toDoc, comma <> space) <> ")"

      case PPointsTo(id, value) => toDoc(id) <+> "|->" <+> toDoc(value)
      case PGuardExp(guard, regionId) => toDoc(guard) <> "@" <> toDoc(regionId)
      case PDiamond(regionId) => toDoc(regionId) <+> "|=>" <+> "<D>"
      case PRegionUpdateWitness(regionId, from, to) =>
        toDoc(regionId) <+> "|=>" <+> "(" <+> toDoc(from) <> "," <+> toDoc(to) <> ")"

      case PIrrelevantValue() => "_"
    }

  def toDoc(typ: PType): Doc =
    typ match {
      case PIntType() => "int"
      case PBoolType() => "bool"
      case PSetType(elementType) => "set" <> brackets(toDoc(elementType))
      case PRefType(referencedType) => toDoc(referencedType) <> asterisk
      case PRegionIdType() => "id"
      case PVoidType() => "void"
      case PUnknownType() => "<unknown>"
    }
}
