/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import scala.language.postfixOps
import org.bitbucket.inkytonik.kiama.parsing.Parsers
import org.bitbucket.inkytonik.kiama.util.Positions

class SyntaxAnalyser(positions: Positions) extends Parsers(positions) {
  override val whitespace: Parser[String] =
    """(\s|(//.*\s*\n))*""".r
//    """(\s|(//.*\s*\n)|\(\*(?:.|[\n\r])*?\*\))*""".r

  val reservedWords = Set(
    "true", "false",
    "void", "int", "bool", "id", "Set",
    "region", "guards", "duplicable", "interpretation", "abstraction", "actions",
    "predicate",
    "interference", "requires", "ensures", "invariant",
    "procedure", "atomic", //"ret",
    "interference", "in", "on",
    "if", "else", "while", "skip", "inhale", "exhale",
    "make_atomic", "update_region",
    "Int", "Nat"
  )

  lazy val program: Parser[PProgram] =
    (region | predicate | procedure).+ ^^ (members => {
      val region = members collect { case p: PRegion => p }
      val predicates = members collect { case p: PPredicate => p }
      val procedures = members collect { case p: PProcedure => p }

      PProgram(region, predicates, procedures)
    })

  lazy val region: Parser[PRegion] =
    ("region" ~> idndef) ~
    ("(" ~> formalArg) ~ (("," ~> formalArgs).? <~ ")") ~
    ("guards" ~> "{" ~> guard.+ <~ "}") ~
    ("interpretation" ~> "{" ~> expression <~ "}") ~
    ("state" ~> "{" ~> expression <~ "}") ~
    ("actions" ~> "{" ~> action.+ <~ "}") ^^ {
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
    "duplicable".? ~ idndef <~ ";" ^^ { case optDup ~ id => PGuardDecl(id, optDup.isDefined) }

  lazy val action: Parser[PAction] =
    (idnuse <~ ":") ~ expression ~ ("~>" ~> expression <~ ";") ^^ PAction

  lazy val predicate: Parser[PPredicate] =
    ("predicate" ~> idndef) ~
    ("(" ~> formalArgs <~ ")") ~
    ("{" ~> expression <~ "}") ^^ {
      case id ~ args ~ body => PPredicate(id, args, body)
    }

  lazy val procedure: Parser[PProcedure] =
    "atomic".? ~
    typeOrVoid ~
    idndef ~ ("(" ~> formalArgs <~ ")") ~
    interference.* ~
    requires.* ~
    ensures .* ~
    (("{" ~> varDeclStmt.*) ~ (statement.* <~ "}")).? ^^ {
      case optAtomic ~ tpe ~ id ~ args ~ inters ~ pres ~ posts ~ optBody =>
        val (locals, body) =
          optBody match {
            case Some(l ~ b) => (l, Some(b))
            case None => (Vector.empty, None)
          }

        PProcedure(id, args, tpe, inters, pres, posts, locals, body, optAtomic.isDefined)
    }

  lazy val formalArgs: Parser[Vector[PFormalArgumentDecl]] =
    repsep(formalArg, ",")

  lazy val formalArg: Parser[PFormalArgumentDecl] =
    typ ~ idndef ^^ { case tpe ~ id => PFormalArgumentDecl(id, tpe) }

  lazy val interference: Parser[PInterferenceClause] =
    ("interference" ~> idnuse <~ "in") ~ setLiteral ~ ("on" ~> idnuse  <~ ";") ^^ PInterferenceClause

  lazy val requires: Parser[PPreconditionClause] =
    "requires" ~> expression <~ ";" ^^ PPreconditionClause

  lazy val ensures: Parser[PPostconditionClause] =
    "ensures" ~> expression <~ ";" ^^ PPostconditionClause

  lazy val invariant: Parser[PInvariantClause] =
    "invariant" ~> expression <~ ";" ^^ PInvariantClause

  lazy val statement: Parser[PStatement] =
    "skip" <~ ";" ^^ (_ => PSkip()) |
    "if" ~> ("(" ~> expression <~ ")") ~ statement ~ ("else" ~> statement).? ^^ PIf |
    ("do" ~> invariant.*) ~ ("{" ~> statement.* <~ "}") ~ ("while" ~> "(" ~> expression <~ ")") <~ ";" ^^ {
      case invs ~ stmts ~ cond => PBlock(stmts :+ PWhile(cond, invs, stmts))
    } |
    "while" ~> ("(" ~> expression <~ ")") ~ invariant.* ~ ("{" ~> statement.* <~ "}") ^^ PWhile |
    "fold" ~> idnuse ~ ("(" ~> listOfExpressions <~ ")") <~ ";" ^^ PFold |
    "unfold" ~> idnuse ~ ("(" ~> listOfExpressions <~ ")") <~ ";" ^^ PUnfold |
    "inhale" ~> expression <~ ";" ^^ PInhale |
    "exhale" ~> expression <~ ";" ^^ PExhale |
    ("*" ~> idnuse) ~ (":=" ~> expression <~ ";") ^^ PHeapWrite |
    makeAtomic |
    updateRegion |
    "{" ~> statement.* <~ "}" ^^ PBlock |
    (idnuse <~ ":=").? ~ idnuse ~ ("(" ~> listOfExpressions <~ ")") <~ ";" ^^ {
      case optRhs ~ proc ~ args => PProcedureCall(proc, args, optRhs)
    } |
    idnuse ~ (":=" ~> "*" ~> idnuse) <~ ";" ^^ { case lhs ~ rhs => PHeapRead(lhs, rhs) } |
    idnuse ~ (":=" ~> expression) <~ ";" ^^ PAssign

  lazy val makeAtomic: Parser[PMakeAtomic] =
    "make_atomic" ~>
    ("using" ~> predicateExp) ~ ("with" ~> guardExp <~ ";") ~
    ("{" ~> statement.* <~ "}") ^^ PMakeAtomic

  lazy val updateRegion: Parser[PUpdateRegion] =
    "update_region" ~>
    ("using" ~> predicateExp <~ ";") ~
    ("{" ~> statement.* <~ "}") ^^ PUpdateRegion

  lazy val varDeclStmt: Parser[PLocalVariableDecl] =
    typ ~ idndef <~ ";" ^^ { case tpe ~ id => PLocalVariableDecl(id, tpe) }

  /* Operator precedences and associativity taken from the following sources:
   *   http://en.cppreference.com/w/cpp/language/operator_precedence
   *   https://en.wikipedia.org/wiki/Logical_connective
   */

  lazy val expression: PackratParser[PExpression] = exp99

  lazy val exp99: PackratParser[PExpression] = /* Right associative */
    exp95 ~ ("?" ~> expression <~ ":") ~ exp99 ^^ PConditional |
    exp95

  lazy val exp95: PackratParser[PExpression] = /* Left associative */
    exp95 ~ ("<==>" ~> exp90) ^^ PEquals |
    exp90

  lazy val exp90: PackratParser[PExpression] = /* Right associative */
    exp85 ~ ("==>" ~> exp90) ^^ { case lhs ~ rhs => PConditional(lhs, rhs, PTrueLit()) } |
    exp85

  lazy val exp85: PackratParser[PExpression] = /* Left associative*/
    exp85 ~ ("||" ~> exp80) ^^ POr |
    exp80

  lazy val exp80: PackratParser[PExpression] = /* Left associative*/
    exp80 ~ ("&&" ~> exp70) ^^ PAnd |
    exp70

  lazy val exp70: PackratParser[PExpression] = /* Left associative*/
    exp70 ~ ("==" ~> exp60) ^^ PEquals |
    exp70 ~ ("!=" ~> exp60) ^^ { case lhs ~ rhs => PNot(PEquals(lhs, rhs)) } |
    exp60

  lazy val exp60: PackratParser[PExpression] = /* Left associative*/
    exp60 ~ ("<" ~> exp50) ^^ PLess |
    exp60 ~ ("<=" ~> exp50) ^^ PAtMost |
    exp60 ~ (">" ~> exp50) ^^ PGreater |
    exp60 ~ (">=" ~> exp50) ^^ PAtLeast |
    exp50

  lazy val exp50: PackratParser[PExpression] = /* Left associative */
    exp50 ~ ("+" ~> exp40) ^^ PAdd |
    exp50 ~ ("-" ~> exp40) ^^ PSub |
    exp40

  lazy val exp40: PackratParser[PExpression] = /* Right associative */
    "+" ~> exp40 |
    "-" ~> exp40 ^^ (e => PSub(PIntLit(0), e)) |
    "!" ~> exp40 ^^ PNot |
    exp0

  lazy val exp0: PackratParser[PExpression] =
    "true" ^^ (_ => PTrueLit()) |
    "false" ^^ (_ => PFalseLit()) |
    "ret" ^^ (_ => PRet()) |
    "_" ^^ (_ => PIrrelevantValue()) |
    setLiteral |
    regex("[0-9]+".r) ^^ (lit => PIntLit(BigInt(lit))) |
    predicateExp |
    (idnuse <~ "|->") ~ binderOrExpression ^^ PPointsTo |
    (idnuse <~ "|=>") ~ ("(" ~> expression) ~ ("," ~> expression <~ ")") ^^ PRegionUpdateWitness |
    idnuse <~ "|=>" <~ "<D>" ^^ PDiamond |
    guardExp |
    idnuse ^^ PIdnExp |
    "(" ~> expression <~ ")"

  lazy val predicateExp: Parser[PPredicateExp] =
    idnuse ~ ("(" ~> listOfExpressions <~ ")") ^^ {
      case callee ~ args => PPredicateExp(callee, args)
    }

  lazy val guardExp: Parser[PGuardExp] =
    (idnuse <~ "@") ~ idnuse ^^ PGuardExp

  lazy val setLiteral: Parser[PLiteral] =
    "Set" ~> "(" ~> listOfExpressions <~ ")" ^^ PExplicitSet |
    "Int" ^^ (_ => PIntSet()) |
    "Nat" ^^ (_=> PNatSet())

  lazy val binderOrExpression: Parser[Either[PLogicalVariableDecl, PExpression]] =
    "?" ~> idndef ^^ (id => Left(PLogicalVariableDecl(id))) |
    expression ^^ (exp => Right(exp))

  lazy val listOfExpressions: Parser[Vector[PExpression]] =
    repsep(expression, ",")

//  lazy val listOfBindersOrExpressions: Parser[Vector[Either[PLogicalVariableDecl, PExpression]]] =
//    repsep(binderOrExpression, ",")

  lazy val typeOrVoid: Parser[PType] =
    "void" ^^ (_ => PVoidType()) |
    typ

  lazy val typ: Parser[PType] =
    "int*" ^^ (_ => PRefType(PIntType())) |
    "int" ^^ (_ => PIntType()) |
    "bool*" ^^ (_ => PRefType(PBoolType())) |
    "bool" ^^ (_ => PBoolType()) |
    "id" ^^ (_ => PRegionIdType())

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
}
