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
      case statement: PStatement => toDoc(statement)
      case expression: PExpression => toDoc(expression)
      case typ: PType => toDoc(typ)

      case _: PPredicateAccess => ???
      case _: PModifier => ???

      case PIdnDef(name) => name
      case PIdnUse(name) => name

      case _: PDeclaration => ???
      case _: PSpecificationClause => ???
      case PAction(guard, from, to) => ???
//      case _: PBindingContext => ???
    }

  def toDoc(program: PProgram): Doc = {
    val PProgram(regions, predicates, procedures) = program

    (    ssep(regions map toDoc, line)
      <> line
      <> ssep(predicates map toDoc, line)
      <> line
      <> ssep(procedures map toDoc, line))
  }

  def toDoc(region: PRegion): Doc = ???
  def toDoc(predicate: PPredicate): Doc = ???

  def toDoc(procedure: PProcedure): Doc = {
    val PProcedure(id, formalArgs, typ, inters, pres, posts, locals, body, atomicity) = procedure

    val signatureDoc =
      toDoc(typ) <+> id.name <> parens(ssep(formalArgs map toDoc, comma <> space))

    val contractDoc = emptyDoc // TODO: Implement

    val bodyDoc = (
         ssep(locals map toDoc, line)
      <> line
      <> body.fold(emptyDoc)(toDoc)) // TODO: Account for abstract procedures

    signatureDoc <> nest(line <> contractDoc) <> braces(nest(line <> bodyDoc))
  }

  def toDoc(statement: PStatement): Doc =
    statement match {
      case _: PCompoundStatement => ???
      case PSkip() => "skip" <> semi
      case PAssign(lhs, rhs) => toDoc(lhs) <+> ":=" <+> toDoc(rhs)
      case PHeapRead(lhs, location) => toDoc(lhs) <+> ":=" <+> "*" <> toDoc(location)
      case PHeapWrite(location, rhs) => "*" <> toDoc(location) <+> ":=" <+> toDoc(rhs)

      case PProcedureCall(procedure, arguments, rhs) => ???
      case _: PGhostStatement => ???
//      case _: PRuleStatement => ???
    }

  def toDoc(expression: PExpression): Doc =
    expression match {
      case PLogicalVariableBinder(id) => "?" <> id.name

      case PTrueLit() => "true"
      case PFalseLit() => "false"
      case PIntLit(value) => value.toString
      case PRet() => "ret"
      case PExplicitSet(args, typeAnnotation) =>
        "Set" <>
          typeAnnotation.fold(emptyDoc)(typ => "[" <> toDoc(typ) <> "]") <>
          "(" <> ssep(args map toDoc, comma <> space) <> ")"
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
        
      case PIdnExp(id) => id.name
      case PPredicateExp(predicate, arguments) =>
        predicate.name <> "(" <> ssep(arguments map toDoc, comma <> space) <> ")"

      case PPointsTo(id, value) => id.name <+> "|->" <+> toDoc(value)
      case PGuardExp(guard, regionId) => guard.name <> "@" <> regionId.name
      case PDiamond(regionId) => regionId.name <+> "|=>" <+> "<D>"
      case PRegionUpdateWitness(regionId, from, to) =>
        regionId.name <+> "|=>" <+> "(" <+> toDoc(from) <> "," <+> toDoc(to) <> ")"

      case PIrrelevantValue() => "_"
    }

  def toDoc(typ: PType): Doc = ???
}
