/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import scala.annotation.switch
import scala.language.postfixOps
import org.bitbucket.inkytonik.kiama.parsing.Parsers
import org.bitbucket.inkytonik.kiama.rewriting.{Cloner, PositionedRewriter}
import org.bitbucket.inkytonik.kiama.util.Positions

class SyntaxAnalyser(positions: Positions) extends Parsers(positions) {
  override val whitespace: Parser[String] =
    """(\s|(//.*\s*\n)|/\*(?s:(.*)?)\*/)*""".r
      // The above regex matches the same whitespace strings as this one:
      //   (\s|(//.*\s*\n)|/\*(?:.|[\n\r])*?\*/)*
      // but (hopefully) avoids potential stack overflows caused by an open issue
      // of Oracle's JDK. See also:
      //   - http://bugs.java.com/bugdatabase/view_bug.do?bug_id=6882582
      //   - https://stackoverflow.com/a/31691056
      //

  val reservedWords = Set(
    "true", "false",
    "void", "int", "bool", "id", "set",
    "region", "guards", "unique", "duplicable", "interpretation", "abstraction", "actions",
    "predicate", "struct",
    "interference", "in", "on", "requires", "ensures", "invariant",
    "abstract_atomic", "primitive_atomic", //"ret",
    "if", "else", "while", "do", "skip",
    "inhale", "exhale", "assume", "assert", "havoc", "use_region_interpretation",
    "make_atomic", "update_region", "use_atomic", "open_region",
    "Int", "Nat", "Set",
    "true", "false", "null",
    "unfolding"
  )

  lazy val program: Parser[PProgram] =
    (struct | region | predicate | procedure).* ^^ (members => {
      val structs = members collect { case p: PStruct => p }
      val regions = members collect { case p: PRegion => p }
      val predicates = members collect { case p: PPredicate => p }
      val procedures = members collect { case p: PProcedure => p }

      PProgram(structs, regions, predicates, procedures)
    })

  lazy val struct: Parser[PStruct] =
    ("struct" ~> idndef) ~
    ("{" ~> (formalArg <~ ";").* <~ "}") ^^ PStruct

  lazy val region: Parser[PRegion] =
    ("region" ~> idndef) ~
    ("(" ~> formalArg) ~ (("," ~> formalArgs).? <~ ")") ~
    ("guards" ~> "{" ~> guard.+ <~ "}") ~
    ("interpretation" ~> "{" ~> expression <~ "}") ~
    ("state" ~> "{" ~> expression <~ "}") ~
    ("actions" ~> "{" ~> action.* <~ "}") ^^ {
      case id ~ regionId ~ optArgs ~ guards ~ interpretation ~ abstraction ~ actions =>
        PRegion(
          id,
          regionId,
          optArgs.getOrElse(Vector.empty),
          guards,
          interpretation,
          abstraction,
          actions)
    }

  lazy val guard: Parser[PGuardDecl] =
    guardModifier ~ idndef <~ ";" ^^ { case mod ~ id => PGuardDecl(id, mod) }

  lazy val guardModifier: Parser[PGuardModifier] =
    "unique" ^^^ PUniqueGuard() |
    "duplicable" ^^^ PDuplicableGuard() |
    success(PUniqueGuard())

  lazy val action: Parser[PAction] =
    (idnuse <~ ":") ~ expression ~ ("~>" ~> expression <~ ";") ^^ PAction1 |
    (idnuse <~ ":") ~ binder ~ ("~>" ~> expression <~ ";") ^^ PAction2 |
    (idnuse <~ ":") ~ binder ~ ("if" ~> expression).? ~ ("~>" ~> expression <~ ";") ^^ {
      case guardId ~ from ~ optConstraint ~ to =>
        PAction3(guardId, from, optConstraint.getOrElse(PTrueLit().at(from)), to)
    }

  lazy val predicate: Parser[PPredicate] =
    ("predicate" ~> idndef) ~
    ("(" ~> formalArgs <~ ")") ~
    ("{" ~> expression <~ "}").? ^^ {
      case id ~ args ~ body => PPredicate(id, args, body)
    }

  lazy val procedure: Parser[PProcedure] =
    atomicityModifier ~
    typeOrVoid ~
    idndef ~ ("(" ~> formalArgs <~ ")") ~
    interference.* ~
    requires.* ~
    ensures .* ~
    (("{" ~> varDeclStmt.*) ~ (statementsOrSkip <~ "}")).? ^^ {
      case mod ~ tpe ~ id ~ args ~ inters ~ pres ~ posts ~ optBraces =>
        val (locals, body) =
          optBraces match {
            case None =>
              /* Abstract method, i.e. braces omitted */
              (Vector.empty, None)
            case Some(l ~ b) =>
              /* Concrete method with at least one statement in the body */
              (l, Some(b))
          }

        PProcedure(id, args, tpe, inters, pres, posts, locals, body, mod)
    }

  lazy val statementsOrSkip: Parser[PStatement] =
    statements | success(PSkip())

  lazy val atomicityModifier: Parser[PAtomicityModifier] =
    "abstract_atomic" ^^^ PAbstractAtomic() |
    "primitive_atomic" ^^^ PPrimitiveAtomic() |
    success(PNotAtomic())

  lazy val formalArgs: Parser[Vector[PFormalArgumentDecl]] =
    repsep(formalArg, ",")

  lazy val formalArg: Parser[PFormalArgumentDecl] =
    typ ~ idndef ^^ { case tpe ~ id => PFormalArgumentDecl(id, tpe) }

  lazy val interference: Parser[PInterferenceClause] =
    "interference" ~> binder ~
    ("in" ~> expression) ~
    ("on" ~> idnuse <~ ";") ^^ PInterferenceClause

  lazy val requires: Parser[PPreconditionClause] =
    "requires" ~> expression <~ ";" ^^ PPreconditionClause

  lazy val ensures: Parser[PPostconditionClause] =
    "ensures" ~> expression <~ ";" ^^ PPostconditionClause

  lazy val invariant: Parser[PInvariantClause] =
    "invariant" ~> expression <~ ";" ^^ PInvariantClause

  lazy val statements: Parser[PStatement] =
    singleStatement ~ statements ^^ PSeqComp | /* Right-associative */
    singleStatement

  lazy val singleStatement: Parser[PStatement] =
    "skip" <~ ";" ^^^ PSkip() |
    "if" ~> ("(" ~> expression <~ ")") ~ ("{" ~> statements <~ "}") ~ ("else" ~> "{" ~> statements <~ "}").? ^^ PIf |
    "while" ~> ("(" ~> expression <~ ")") ~ invariant.* ~ ("{" ~> statements <~ "}") ^^ PWhile |
    parseAndUnrollDoWhileLoop ^^ { case unrolled ~ loop => PSeqComp(unrolled, loop) } |
    "fold" ~> idnuse ~ ("(" ~> listOfExpressions <~ ")") <~ ";" ^^ PFold |
    "unfold" ~> idnuse ~ ("(" ~> listOfExpressions <~ ")") <~ ";" ^^ PUnfold |
    "inhale" ~> expression <~ ";" ^^ PInhale |
    "exhale" ~> expression <~ ";" ^^ PExhale |
    "assume" ~> expression <~ ";" ^^ PAssume |
    "assert" ~> expression <~ ";" ^^ PAssert |
    "havoc" ~> idnuse <~ ";" ^^ PHavoc |
    "use_region_interpretation" ~> predicateExp <~ ";" ^^ PUseRegionInterpretation |
    makeAtomic |
    updateRegion |
    useAtomic |
    openRegion |
    "(" ~> statements <~ ")" <~ ";" |
    (idnuse <~ ":=").? ~ idnuse ~ ("(" ~> listOfExpressions <~ ")") <~ ";" ^^ {
      case optRhs ~ proc ~ args => PProcedureCall(proc, args, optRhs)
    } |
    idnuse ~ (":=" ~> location) <~ ";" ^^ { case lhs ~ rhs => PHeapRead(lhs, rhs) } |
    location ~ (":=" ~> expression <~ ";") ^^ PHeapWrite |
    idnuse ~ (":=" ~> expression) <~ ";" ^^ PAssign

  lazy val location: Parser[PLocation] =
    idnuse ~ ("." ~> idnuse) ^^ PLocation

  /* Parses and unrolls a do-while loop.
   * Several hack-ish steps are performed to avoid node sharing while ensuring correct
   * position information bookkeeping.
   */
  private lazy val parseAndUnrollDoWhileLoop: Parser[~[PStatement, PWhile]] =
    parseDoWhileLoop ^^ {
      case tuple @ (invs, stmts, cond) =>
        /* Since the tuple is obtained from a parser (i.e. returned as a `Parser[...]`) its
         * position has been recorded in `this.positions`. We assign this position to the
         * synthesised while-loop node.
         */
        val loop = PWhile(cond, invs, positionedRewriter.deepclone(stmts))
        positions.dupPos(tuple, loop)

        new ~(stmts, loop)
    }

  /* Parses a do-while loop and returns a tuple with all constituents of the loop.
   * The tuple's position, looked up in `this.positions`, spans the whole do-while loop.
   */
  lazy val parseDoWhileLoop: Parser[(Vector[PInvariantClause], PStatement, PExpression)] =
    ("do" ~> invariant.*) ~ ("{" ~> statements <~ "}") ~ ("while" ~> "(" ~> expression <~ ")") <~ ";" ^^ {
      case invs ~ stmts ~ cond => (invs, stmts, cond)
    }

  lazy val makeAtomic: Parser[PMakeAtomic] =
    "make_atomic" ~>
    ("using" ~> predicateExp) ~ ("with" ~> guardExp <~ ";") ~
    ("{" ~> statements <~ "}") ^^ PMakeAtomic

  lazy val updateRegion: Parser[PUpdateRegion] =
    "update_region" ~>
    ("using" ~> predicateExp <~ ";") ~
    ("{" ~> statements <~ "}") ^^ PUpdateRegion

  lazy val useAtomic: Parser[PUseAtomic] =
    "use_atomic" ~>
    ("using" ~> predicateExp) ~ ("with" ~> guardExp <~ ";") ~
    ("{" ~> statements <~ "}") ^^ PUseAtomic

  lazy val openRegion: Parser[POpenRegion] =
    "open_region" ~>
    ("using" ~> predicateExp <~ ";") ~
    ("{" ~> statements <~ "}") ^^ POpenRegion

  lazy val varDeclStmt: Parser[PLocalVariableDecl] =
    typ ~ idndef <~ ";" ^^ { case tpe ~ id => PLocalVariableDecl(id, tpe) }

  /* Operator precedences and associativity taken from the following sources:
   *   http://en.cppreference.com/w/cpp/language/operator_precedence
   *   https://en.wikipedia.org/wiki/Logical_connective
   */

  lazy val expression: PackratParser[PExpression] = exp99

  lazy val exp99: PackratParser[PExpression] = /* Right-associative */
    exp95 ~ ("?" ~> expression <~ ":") ~ exp99 ^^ PConditional |
    exp95

  lazy val exp95: PackratParser[PExpression] = /* Left-associative */
    exp95 ~ ("<==>" ~> exp90) ^^ PEquals |
    exp90

  lazy val exp90: PackratParser[PExpression] = /* Right-associative */
    exp85 ~ ("==>" ~> exp90) ^^ {
      case lhs ~ rhs => PConditional(lhs, rhs, PTrueLit().at(lhs))
    } |
    exp85

  lazy val exp85: PackratParser[PExpression] = /* Left-associative*/
    exp85 ~ ("||" ~> exp80) ^^ POr |
    exp80

  lazy val exp80: PackratParser[PExpression] = /* Left-associative*/
    exp80 ~ ("&&" ~> exp70) ^^ PAnd |
    exp70

  lazy val exp70: PackratParser[PExpression] = /* Left-associative*/
    exp70 ~ ("==" ~> exp60) ^^ PEquals |
    exp70 ~ ("!=" ~> exp60) ^^ {
      case lhs ~ rhs => PNot(PEquals(lhs, rhs).range(lhs, rhs))
    } |
    exp60

//  lazy val exp60: PackratParser[PExpression] = /* Left-associative*/
//    exp60 ~ ("<=" ~> exp50) ^^ PAtMost |
//    exp60 ~ ("<" ~> exp50) ^^ PLess |
//    exp60 ~ (">=" ~> exp50) ^^ PAtLeast |
//    exp60 ~ (">" ~> exp50) ^^ PGreater |
//    exp60 ~ ("in" ~> exp50) ^^ PSetContains |
//    exp50

  lazy val ineqOps: Parser[String] =
    /* Note: Operators have to be ordered in descending prefix order, i.e.
     *       '<=' must come before '<'.
     */
    "<=" | "<" | ">=" | ">"

  lazy val exp60: PackratParser[PExpression] =
    exp60 ~ ("in" ~> exp50) ^^ PSetContains | /* Left-associative */
    exp50 ~ (ineqOps ~ exp50).* ^^ { /* TODO: Figure out associativity */
      case exp ~ Seq() =>
        exp
      case exp ~ chain =>
        val init = (exp, Vector.empty[PBinOp])

        val (_, comparisons) =
          chain.foldLeft(init) {
            case ((left, result), sym ~ right) =>
              val op =
                /* TODO: Avoid duplicating operators from rule ineqOps above */
                (sym: @switch) match {
                  case "<" => PLess
                  case "<=" => PAtMost
                  case ">" => PGreater
                  case ">=" => PAtLeast
                }

              (positionedRewriter.deepclone(right),
               result :+ op(left, right).range(left, right))
          }

        comparisons.tail.foldLeft(comparisons.head) { case (exp1, exp2) =>
          PAnd(exp1, exp2).range(exp1, exp2)
        }
    }

  lazy val exp50: PackratParser[PExpression] = /* Left-associative */
    exp50 ~ ("+" ~> exp40) ^^ PAdd |
    exp50 ~ ("-" ~> exp40) ^^ PSub |
    exp40

  lazy val exp40: PackratParser[PExpression] = /* Right-associative */
    "+" ~> exp40 |
    "-" ~> exp40 ^^ (e => PSub(PIntLit(0).at(e), e)) |
    "!" ~> exp40 ^^ PNot |
    exp0

  lazy val exp0: PackratParser[PExpression] =
    "true" ^^^ PTrueLit() |
    "false" ^^^ PFalseLit() |
    "null" ^^^ PNullLit() |
    "ret" ^^^ PRet() |
    "_" ^^^ PIrrelevantValue() |
    ("unfolding" ~> predicateExp <~ "in") ~ expression ^^ PUnfolding |
    regex("[0-9]+".r) ^^ (lit => PIntLit(BigInt(lit))) |
    setExpression |
    predicateExp |
    (location <~ "|->") ~ binderOrExpression ^^ PPointsTo |
    (idnuse <~ "|=>") ~ ("(" ~> expression) ~ ("," ~> expression <~ ")") ^^ PRegionUpdateWitness |
    idnuse <~ "|=>" <~ "<D>" ^^ PDiamond |
    guardExp |
    idnuse ^^ PIdnExp |
    "(" ~> expression <~ ")"

  lazy val predicateExp: Parser[PPredicateExp] =
    idnuse ~ ("(" ~> listOfBindersOrExpressions <~ ")") ^^ {
      case callee ~ args => PPredicateExp(callee, args)
    }

  lazy val guardExp: Parser[PGuardExp] =
    (idnuse <~ "@") ~ idnuse ^^ PGuardExp

  lazy val setExpression: Parser[PSetExp] =
    setLiteral | setComprehension

  lazy val setLiteral: Parser[PSetExp with PLiteral] =
    "Set" ~> ("[" ~> typ <~ "]").? ~ ("(" ~> listOfExpressions <~ ")") ^^ {
      case typeAnnotation ~ elements => PExplicitSet(elements, typeAnnotation)
    } |
    "Int" ^^^ PIntSet() |
    "Nat" ^^^ PNatSet()

  lazy val setComprehension: Parser[PSetComprehension] =
    "Set" ~> ("[" ~> typ <~ "]").? ~ ("(" ~> binder) ~ ("|" ~> expression) <~ ")" ^^ {
      case typeAnnotation ~ qvar ~ filter => PSetComprehension(qvar, filter, typeAnnotation)
    }

  lazy val binder: Parser[PLogicalVariableBinder] =
    "?" ~> idndef ^^ (id => PLogicalVariableBinder(id))

  lazy val binderOrExpression: Parser[PExpression] =
    "?" ~> idndef ^^ (id => PLogicalVariableBinder(id)) |
    expression

  lazy val listOfExpressions: Parser[Vector[PExpression]] =
    repsep(expression, ",")

  lazy val listOfBindersOrExpressions: Parser[Vector[PExpression]] =
    repsep(binderOrExpression, ",")

  lazy val typeOrVoid: Parser[PType] =
    "void" ^^^ PVoidType() |
    typ

  lazy val typ: PackratParser[PType] =
    "int" ^^^ PIntType() |
    "bool" ^^^ PBoolType() |
    "id" ^^^ PRegionIdType() |
    "set" ~> "<" ~> typ <~ ">" ^^ PSetType |
    idnuse ^^ PRefType

  lazy val idndef: Parser[PIdnDef] =
    identifier ^^ PIdnDef

  lazy val idnuse: Parser[PIdnUse] =
    identifier ^^ PIdnUse

  lazy val identifier: Parser[String] =
    "[a-zA-Z][a-zA-Z0-9_]*".r into (s => {
      if (reservedWords contains s)
        failure(s"""keyword "$s" found where identifier expected""")
      else
        success(s)
    })

  object positionedRewriter extends PositionedRewriter with Cloner {
    override val positions: Positions = SyntaxAnalyser.this.positions
  }

  implicit class PositionedPAstNode[N <: PAstNode](node: N) {
    def at(other: PAstNode): N = {
      positions.dupPos(other, node)
    }

    def range(from: PAstNode, to: PAstNode): N = {
      positions.dupRangePos(from, to, node)
    }
  }
}
