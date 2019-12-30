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
      case arg: PGuardArg => toDoc(arg)
    }

  def toDoc(action: PAction): Doc = {
    val PAction(binders, condition, guards, from, to) = action

    val bindersDoc =
      if (binders.isEmpty) emptyDoc
      else ssep(binders map toDoc, comma <> space) <+> "|" <> space

    val constraintDoc =
      condition match {
        case _: PTrueLit => emptyDoc
        case _ => toDoc(condition) <+> "|" <> space
      }

    val guardsDoc = parens(ssep(guards map toDoc, comma <> space))

    bindersDoc <> constraintDoc <> guardsDoc <> ":" <+> toDoc(from) <+> "~>" <+> toDoc(to)
  }

  def toDoc(clause: PSpecificationClause): Doc = {
    clause match {
      case PPreconditionClause(assertion) => "requires" <+> toDoc(assertion)
      case PPostconditionClause(assertion) => "ensures" <+> toDoc(assertion)
      case PInvariantClause(assertion) => "invariant" <+> toDoc(assertion)

      case PInterferenceClause(variable, set, optRegion) =>
        val onDoc = optRegion match {
          case None => emptyDoc
          case Some(region) => " on" <+> toDoc(region)
        }

        (  "interference" <+> toDoc(variable)
         <+> "in" <+> toDoc(set)
         <> onDoc)
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
      case PDivisibleGuard() => "divisible"
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
      case PNamedBinder(id, typeAnnotation) =>
        typeAnnotation.fold(emptyDoc)(typ => toDoc(typ) <> space) <> "?" <> toDoc(id)
      case PGuardDecl(id, args, modifier) =>
        toDoc(modifier) <+> toDoc(id) <> asFormalArguments(args)
    }
  }

  def toDoc(declaration: PNamedBinder): Doc =
    toDoc(declaration: PDeclaration)

  def toDoc(member: PMember): Doc = {
    member match {
      case PStruct(id, fields) =>
        "struct" <+> toDoc(id) <+>
        block(lterm(fields map toDoc, semi))

      case PRegion(id, formalInArgs, formalOutArgs, guards, interpretation, state, actions, fields) =>
        "region" <+> toDoc(id) <>
        "ghost_fields" <+> block(lterm(fields map toDoc, semi)) <@>
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
        "macro" <+> toDoc(id) <+> (
        formalArguments match {
          case Some(args) => parens(ssep(args map toDoc, comma))
          case None => emptyDoc
        }) <+>
        toDoc(body) <> semi

      case PStatementMacro(id, formalArguments, locals, body) =>
        "macro" <+> toDoc(id) <+> parens(ssep(formalArguments map toDoc, comma)) <+>
        braces(nest(ssep(locals map toDoc, semi) <> line <> toDoc(body)))

      case PTypeMacro(id, formalArguments, body) =>
        "macro" <+> toDoc(id) <+> (
        formalArguments match {
          case Some(args) => parens(ssep(args map toDoc, comma))
          case None => emptyDoc
        }) <+>
        toDoc(body) <> semi
    }
  }

  def toDoc(statement: PStatement): Doc =
    statement match {
      case rule: PRuleStatement => toDoc(rule)
      case ghost: PGhostStatement => toDoc(ghost)
      case PSeqComp(first, second) => toDoc(first) <> line <> toDoc(second)
      case PSkip() => "skip" <> semi

      case PNewStmt(lhs, constructor, arguments, guards, initializer) =>
        val initializerDoc =
          initializer.fold(emptyDoc)(stmt => space <> braces(nest(toDoc(stmt))))

        val guardsDoc =
          guards.fold(emptyDoc)(guards => space <> "with" <+> asBaseGuards(guards))

        toDoc(lhs) <+> ":=" <+> "new" <+> toDoc(constructor) <> asArguments(arguments) <>
          guardsDoc <>
          initializerDoc

      case PAssign(lhs, rhs) => toDoc(lhs) <+> ":=" <+> toDoc(rhs) <> semi
      case PHeapRead(lhs, location) => toDoc(lhs) <+> ":=" <+> toDoc(location) <> semi
      case PHeapWrite(location, rhs) => toDoc(location) <+> ":=" <+> toDoc(rhs) <> semi

      case PIf(cond, thn, optEls) =>
        val elseDoc = optEls match {
          case None => emptyDoc
          case Some(els) => "else" <> braces(nest(toDoc(els)))
        }

        "if" <> parens(toDoc(cond)) <> braces(nest(toDoc(thn))) <> elseDoc

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
      case PLemmaApplication(call) => "use" <+> toDoc(call)<> semi
      case PUseRegionInterpretation(regionPredicate) =>
        "use_region_interpretation" <+> toDoc(regionPredicate) <> semi
      case other =>
        sys.error(s"Implementation missing for element of class ${other.getClass.getSimpleName}")
    }
  }

  def asArguments(arguments: Vector[PExpression]): Doc =
    parens(ssep(arguments map toDoc, comma <> space))

  def asFormalArguments(arguments: Vector[PFormalArgumentDecl]): Doc =
    parens(ssep(arguments map toDoc, comma <> space))

  def asFormalReturns(returns: Vector[PFormalReturnDecl]): Doc =
    parens(ssep(returns map toDoc, comma <> space))

  def asBaseGuards(arguments: Vector[PBaseGuardExp]): Doc =
    ssep(arguments map toDoc, space <> "&&" <> space)

  def toDoc(rule: PRuleStatement): Doc = {
    rule match {
      case PMakeAtomic(regionPredicate, guards, body) =>
        (   "make_atomic" <> line
         <> nest("using" <+> toDoc(regionPredicate) <+> "with" <+> ssep(guards map toDoc, comma <> space) <> semi) <> line
         <> braces(nest(toDoc(body))))
      case PUseAtomic(regionPredicate, guards, body) =>
        (   "use_atomic" <> line
         <> nest("using" <+> toDoc(regionPredicate) <+> "with" <+> ssep(guards map toDoc, comma <> space) <> semi) <> line
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
      case binder: PNamedBinder => toDoc(binder: PDeclaration)
      case PAnonymousBinder() => "_"
      case PFracLiteral(_, _) => ???

      case PUnfolding(predicate, body) =>
        "unfolding" <+> toDoc(predicate) <+> "in" <+> toDoc(body)

      /* TODO: Unify cases for PExplicitSet, PExplicitSeq and PExplicitTuple */

      case PExplicitSet(args, typeAnnotation) =>
        "Set" <>
        typeAnnotation.fold(emptyDoc)(typ => "[" <> toDoc(typ) <> "]") <>
        "(" <> ssep(args map toDoc, comma <> space) <> ")"

      case PExplicitSeq(args, typeAnnotation) =>
        "Seq" <>
        typeAnnotation.fold(emptyDoc)(typ => "[" <> toDoc(typ) <> "]") <>
        "(" <> ssep(args map toDoc, comma <> space) <> ")"

      case PExplicitTuple(elements, typeAnnotation) =>
        s"Tuple${elements.length}" <>
        typeAnnotation.fold(emptyDoc)(ta => "[" <> ssep(ta map toDoc, comma <> space) <> "]") <>
        "(" <> ssep(elements map toDoc, comma <> space) <> ")"

      case PExplicitMap(elements, typeAnnotation) =>
        val elementsDoc =
          elements map { case (key, value) => toDoc(key) <+> ":=" <+> toDoc(value) }

        "Map" <>
        typeAnnotation.fold(emptyDoc)(ta =>
          "[" <> ssep(Vector(ta._1, ta._2) map toDoc, comma <> space) <> "]") <>
        "(" <> ssep(elementsDoc, comma <> space) <> ")"

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
      case PSetSubset(left, right) => parens(toDoc(left) <+> "subset" <+> toDoc(right))
      case PSetUnion(left, right) => parens(toDoc(left) <+> "union" <+> toDoc(right))
      case PSeqSize(seq) => "size" <> parens(toDoc(seq))
      case PSeqHead(seq) => "head" <> parens(toDoc(seq))
      case PSeqTail(seq) => "tail" <> parens(toDoc(seq))
      case PSeqConcat(left, right) => parens(toDoc(left) <+> "concat" <+> toDoc(right))
      case PTupleGet(tuple,index) => s"get$index" <> parens(toDoc(tuple))
      case PMapUnion(left, right) => "uni" <> parens(toDoc(left) <> comma <+> toDoc(right))
      case PMapDisjoint(left, right) => "disj" <> parens(toDoc(left) <> comma <+> toDoc(right))
      case PMapKeys(map) => "keys" <> parens(toDoc(map))
      case PMapLookup(map, key) => "lkup" <> parens(toDoc(map) <> comma <+> toDoc(key))
      case PMapContains(_, _) => ???
      case PMapUpdate(_, _, _) => ???
      case PMapValues(_)  => ???

      case PConditional(cond, thn, els) =>
        parens(toDoc(cond) <+> "?" <+> toDoc(thn) <+> ":" <+> toDoc(els))

      case PPredicateExp(predicate, arguments) =>
        toDoc(predicate) <> "(" <> ssep(arguments map toDoc, comma <> space) <> ")"

      case PPointsTo(id, value) => toDoc(id) <+> "|->" <+> toDoc(value)
      case PDiamond(regionId) => toDoc(regionId) <+> "|=>" <+> "<D>"

      case PRegionedGuardExp(guard, regionId, argument) =>
        toDoc(guard) <> toDoc(argument) <> "@" <> toDoc(regionId)

      case PBaseGuardExp(guard, argument) =>
        toDoc(guard) <> toDoc(argument)

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
      case PTupleType(elementTypes) =>
        s"tuple${elementTypes.length}" <> angles(ssep(elementTypes map toDoc, comma <> space))
      case PMapType(elementType1, elementType2) =>
        "map" <> angles(toDoc(elementType1) <> "," <+> toDoc(elementType2))
      case PRefType(referencedType) => toDoc(referencedType)
      case PRegionIdType() => "id"
      case PUnknownType() => "<unknown>"
      case PNullType() => "<null>"
    }

      def toDoc(arg: PGuardArg): Doc =
        arg match {
          case PStandardGuardArg(args) =>
            asArguments(args)
          case PSetGuardArg(set) =>
            "|" <> toDoc(set) <> "|"
        }
}
