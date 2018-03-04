/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama
import scala.collection.immutable

trait PrettyPrinter {
  def format(node: PAstNode): String
}

trait PrettyPrinterCombinators { this: kiama.output.PrettyPrinter =>
  def section(fn: immutable.Seq[Doc] => Doc,
              docs: immutable.Seq[Doc],
              gap: Doc = emptyDoc)
             : Doc = {

    if (docs.isEmpty)
      emptyDoc
    else
      fn(docs) <> line <> gap <> line
  }

  def ssection(fn: (immutable.Seq[Doc], Doc) => Doc,
               docs: immutable.Seq[Doc],
               sep: Doc,
               gap: Doc = emptyDoc)
              : Doc = {

    if (docs.isEmpty)
      emptyDoc
    else
      fn(docs, sep) <> line <> gap <> line
  }

  def block(doc: Doc): Doc = {
    braces(nest(doc) <> line)
  }

  /** A copy of Kiama's `lterm` that omits the preceding linebreak. */
  def lterm2(ds : immutable.Seq[Doc], term: Doc) : Doc =
    if (ds.isEmpty)
      emptyDoc
    else
      folddoc(ds, _ <> term <@> _) <> term
}

class DefaultPrettyPrinter
    extends PrettyPrinter
       with kiama.output.PrettyPrinter
       with PrettyPrinterCombinators {

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
      case modifier: PModifier => toDoc(modifier)
      case id: PIdnNode => toDoc(id)
      case clause: PSpecificationClause => toDoc(clause)
      case action: PAction => toDoc(action)
      case location: PLocation => toDoc(location)
    }

  def toDoc(action: PAction): Doc = {
    val PAction(binders, condition, guardId, guardArguments, from, to) = action

    val bindersDoc =
      if (binders.isEmpty) emptyDoc
      else ssep(binders map toDoc, comma <> space) <+> "|" <> space

    val constraintDoc =
      condition match {
        case _: PTrueLit => emptyDoc
        case _ => toDoc(condition) <+> "|" <> space
      }

    val guardDoc =
      toDoc(guardId) <>
      (if (guardArguments.isEmpty) emptyDoc else asArguments(guardArguments))

    bindersDoc <> constraintDoc <> guardDoc <> ":" <+> toDoc(from) <+> "~>" <+> toDoc(to)
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
      case PNonAtomic() => "non_atomic"
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

    ssection(vsep, structs map toDoc, line) <>
    ssection(vsep, regions map toDoc, line) <>
    ssection(vsep, predicates map toDoc, line) <>
    ssection(vsep, procedures map toDoc, line)
  }

  def toDoc(declaration: PDeclaration): Doc = {
    declaration match {
      case member: PMember => toDoc(member)
      case PFormalArgumentDecl(id, typ) => toDoc(typ) <+> toDoc(id)
      case PFormalReturnDecl(id, typ) => toDoc(typ) <+> toDoc(id)
      case PLocalVariableDecl(id, typ) =>  toDoc(typ) <+> toDoc(id)
      case PNamedBinder(id) =>  "?" <> toDoc(id)
      case PGuardDecl(id, args, modifier) => toDoc(modifier) <+> toDoc(id) <> asFormalArguments(args)
    }
  }

  def toDoc(declaration: PNamedBinder): Doc =
    toDoc(declaration: PDeclaration)

  def toDoc(member: PMember): Doc = {
    member match {
      case PStruct(id, fields) =>
        "struct" <+> toDoc(id) <+>
        block(lterm(fields map toDoc, semi))

      case PRegion(id, formalInArgs, formalOutArgs, guards, interpretation, state, actions) =>
        "region" <+> toDoc(id) <>
        asFormalArguments(formalInArgs) <>
        (formalOutArgs match {
          case Seq() => emptyDoc
          case args => semi <+> ssep(args map toDoc, comma)
        }) <>
        nest(
          line <>
          "guards" <+> block(lterm(guards map toDoc, semi)) <@>
          "interpretation" <+> block(line <> toDoc(interpretation)) <@>
          "state" <+> block(line <> toDoc(state)) <@>
          "actions" <+> block(lterm(actions map toDoc, semi)))

      case PProcedure(id, formalArgs, formalReturns, inters, pres, posts, locals, optBody, atomicity) =>
        toDoc(atomicity) <+> "procedure" <+>
        toDoc(id) <> asFormalArguments(formalArgs) <> (
          if (formalReturns.isEmpty)
            emptyDoc
          else
            space <> "returns" <+> asFormalReturns(formalReturns)
        ) <>
        nest(lterm(inters map toDoc, semi)) <>
        nest(lterm(pres map toDoc, semi)) <>
        nest(lterm(posts map toDoc, semi)) <> (
        optBody match {
          case None =>
            require(locals.isEmpty)
            emptyDoc
          case Some(body) =>
            (if (inters.nonEmpty || pres.nonEmpty || posts.nonEmpty) line else space) <>
            block(
              line <>
              ssection(lterm2, locals map toDoc, semi) <>
              toDoc(body))
        })

      case PPredicate(id, formalArgs, optBody) =>
        "predicate" <+> toDoc(id) <> asFormalArguments(formalArgs) <+>
        (optBody match {
          case None => emptyDoc
          case Some(body) => block(line <> toDoc(body))
        })

      case PExpressionMacro(id, formalArguments, body) =>
        "macro" <+> (
        formalArguments match {
          case Some(args) => parens(ssep(args map toDoc, comma))
          case None => emptyDoc
        }) <+>
        toDoc(body) <> semi

      case PStatementMacro(id, formalArguments, locals, body) =>
        "macro" <+> parens(ssep(formalArguments map toDoc, comma)) <+>
        braces(nest(ssep(locals map toDoc, semi) <> line <> toDoc(body)))
    }
  }

  def toDoc(statement: PStatement): Doc =
    statement match {
      case rule: PRuleStatement => toDoc(rule)
      case ghost: PGhostStatement => toDoc(ghost)
      case PSeqComp(first, second) => toDoc(first) <> line <> toDoc(second)
      case PSkip() => "skip" <> semi
      case PAssign(lhs, rhs) => toDoc(lhs) <+> ":=" <+> toDoc(rhs) <> semi
      case PHeapRead(lhs, location) => toDoc(lhs) <+> ":=" <+> toDoc(location) <> semi
      case PHeapWrite(location, rhs) => toDoc(location) <+> ":=" <+> toDoc(rhs) <> semi

      case _: PIf => ???

      case PWhile(cond, invariants, body) =>
        (   "while" <> parens(toDoc(cond)) <> line
         <> nest(ssep(invariants map toDoc, semi <> line)) <> line
         <> braces(nest(toDoc(body))))

      case PProcedureCall(procedure, arguments, rhs) =>
        val lhsDoc = toDoc(procedure) <> asArguments(arguments)

        if (rhs.isEmpty) lhsDoc
        else ssep(rhs map toDoc, comma <> space) <+> ":=" <+> lhsDoc
    }

  def toDoc(statement: PGhostStatement): Doc = {
    statement match {
      case PFold(predicateExp) => "fold" <+> toDoc(predicateExp) <> semi
      case PUnfold(predicateExp) => "unfold" <+> toDoc(predicateExp) <> semi
      case PInhale(assertion) => "inhale" <+> toDoc(assertion) <> semi
      case PExhale(assertion) => "exhale" <+> toDoc(assertion) <> semi
      case PAssume(assertion) => "assume" <+> toDoc(assertion) <> semi
      case PAssert(assertion) => "assert" <+> toDoc(assertion) <> semi
      case PHavocVariable(variable) => "havoc" <+> toDoc(variable) <> semi
      case PHavocLocation(location) => "havoc" <+> toDoc(location) <> semi
    }
  }

  def asArguments(arguments: Vector[PExpression]): Doc =
    parens(ssep(arguments map toDoc, comma <> space))

  def asFormalArguments(arguments: Vector[PFormalArgumentDecl]): Doc =
    parens(ssep(arguments map toDoc, comma <> space))

  def asFormalReturns(returns: Vector[PFormalReturnDecl]): Doc =
    parens(ssep(returns map toDoc, comma <> space))

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
      case PTrueLit() => "true"
      case PFalseLit() => "false"
      case PNullLit() => "null"
      case PIntLit(value) => value.toString
      case PFullPerm() => "1f"
      case PNoPerm() => "0f"
      case PIdnExp(id) => toDoc(id)
      case PNamedBinder(id) => "?" <> toDoc(id)
      case PAnonymousBinder() => "_"

      case PUnfolding(predicate, body) =>
        "unfolding" <+> toDoc(predicate) <+> "in" <+> toDoc(body)

      /* TODO: Unify cases for PExplicitSet, PExplicitSeq and PExplicitPair */

      case PExplicitSet(args, typeAnnotation) =>
        "Set" <>
        typeAnnotation.fold(emptyDoc)(typ => "[" <> toDoc(typ) <> "]") <>
        "(" <> ssep(args map toDoc, comma <> space) <> ")"

      case PExplicitSeq(args, typeAnnotation) =>
        "Seq" <>
        typeAnnotation.fold(emptyDoc)(typ => "[" <> toDoc(typ) <> "]") <>
        "(" <> ssep(args map toDoc, comma <> space) <> ")"

      case PExplicitPair(elem1, elem2, typeAnnotation) =>
        "Pair" <>
        typeAnnotation.fold(emptyDoc)(ta =>
          "[" <> ssep(Vector(ta._1, ta._2) map toDoc, comma <> space) <> "]") <>
        "(" <> ssep(Vector(elem1, elem2) map toDoc, comma <> space) <> ")"

      case PSetComprehension(qvar, filter, typeAnnotation) =>
        "Set" <>
        typeAnnotation.fold(emptyDoc)(typ => "[" <> toDoc(typ) <> "]") <>
        "(" <> toDoc(qvar) <+> "|" <+> toDoc(filter) <> ")"

      case PIntSet() => "Int"
      case PNatSet() => "Nat"

      case PNot(operand) => "!" <> toDoc(operand)

      /* TODO: Use associativity and precedence to avoid unnecessary parentheses */
      case PEquals(left, right) => parens(toDoc(left) <+> "==" <+> toDoc(right))
      case PAnd(left, right) => parens(toDoc(left) <+> "&&" <+> toDoc(right))
      case POr(left, right) => parens(toDoc(left) <+> "||" <+> toDoc(right))
      case PLess(left, right) => parens(toDoc(left) <+> "<" <+> toDoc(right))
      case PAtMost(left, right) => parens(toDoc(left) <+> "<=" <+> toDoc(right))
      case PGreater(left, right) => parens(toDoc(left) <+> ">" <+> toDoc(right))
      case PAtLeast(left, right) => parens(toDoc(left) <+> ">=" <+> toDoc(right))
      case PAdd(left, right) => parens(toDoc(left) <+> "+" <+> toDoc(right))
      case PSub(left, right) => parens(toDoc(left) <+> "-" <+> toDoc(right))
      case PMul(left, right) => parens(toDoc(left) <+> "*" <+> toDoc(right))
      case PFrac(left, right) => parens(toDoc(left) <+> "/" <+> toDoc(right))
      case PMod(left, right) => parens(toDoc(left) <+> "mod" <+> toDoc(right))
      case PDiv(left, right) => parens(toDoc(left) <+> "div" <+> toDoc(right))
      case PSetContains(element, set) => parens(toDoc(element) <+> "in" <+> toDoc(set))
      case PSetUnion(left, right) => parens(toDoc(left) <+> "union" <+> toDoc(left))
      case PSeqSize(seq) => "size" <> parens(toDoc(seq))
      case PSeqHead(seq) => "head" <> parens(toDoc(seq))
      case PSeqTail(seq) => "tail" <> parens(toDoc(seq))
      case PPairFirst(pair) => "fst" <> parens(toDoc(pair))
      case PPairSecond(pair) => "snd" <> parens(toDoc(pair))

      case PConditional(cond, thn, els) =>
        parens(toDoc(cond) <+> "?" <+> toDoc(thn) <+> ":" <+> toDoc(els))

      case PPredicateExp(predicate, arguments) =>
        toDoc(predicate) <> "(" <> ssep(arguments map toDoc, comma <> space) <> ")"

      case PPointsTo(id, value) => toDoc(id) <+> "|->" <+> toDoc(value)
      case PDiamond(regionId) => toDoc(regionId) <+> "|=>" <+> "<D>"

      case PGuardExp(guard, arguments) =>
        toDoc(guard) <> asArguments(arguments.tail) <> "@" <> toDoc(arguments.head)

      case PRegionUpdateWitness(regionId, from, to) =>
        toDoc(regionId) <+> "|=>" <+> "(" <+> toDoc(from) <> "," <+> toDoc(to) <> ")"
    }

  def toDoc(typ: PType): Doc =
    typ match {
      case PIntType() => "int"
      case PBoolType() => "bool"
      case PFracType() => "frac"
      case PSetType(elementType) => "set" <> angles(toDoc(elementType))
      case PSeqType(elementType) => "seq" <> angles(toDoc(elementType))
      case PPairType(elementType1, elementType2) =>
        "pair" <> angles(toDoc(elementType1) <> "," <+> toDoc(elementType2))
      case PRefType(referencedType) => toDoc(referencedType)
      case PRegionIdType() => "id"
      case PUnknownType() => "<unknown>"
      case PNullType() => "<null>"
    }
}
