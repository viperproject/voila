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

  val reservedWords = Set(
    "true", "false",
    "void", "int", "bool",
    "if", "else", "while"
  )

  lazy val program: Parser[PProgram] =
    (procedure+) ^^ PProgram

  lazy val procedure: Parser[PProcedure] =
    typeOrVoid ~
    idndef ~ ("(" ~> formalArgs <~ ")") ~
    ("{" ~> (varDeclStmt*))  ~ ((statement*) <~ "}") ^^ {
      case tpe ~ id ~ args ~ locals ~ body => PProcedure(id, args, tpe, locals, body) }

  lazy val formalArgs: Parser[Vector[PFormalArgumentDecl]] =
    repsep(formalArg, ",")

  lazy val formalArg: Parser[PFormalArgumentDecl] =
    typ ~ idndef ^^ { case tpe ~ id => PFormalArgumentDecl(id, tpe) }

  lazy val statement: Parser[PStatement] =
    "if" ~> ("(" ~> expression <~ ")") ~ statement ~ ("else" ~> statement) ^^ PIf |
    "while" ~> ("(" ~> expression <~ ")") ~ statement ^^ PWhile |
    ("[" ~> idnuse <~ "]") ~ (":=" ~> expression <~ ";") ^^ PHeapWrite |
    "{" ~> (statement*) <~ "}" ^^ PBlock |
    idnuse ~ (":=" ~> "[" ~> idnuse <~ "]") <~ ";" ^^ { case lhs ~ rhs => PHeapRead(lhs, rhs) } |
    idnuse ~ (":=" ~> expression) <~ ";" ^^ PAssign

  lazy val varDeclStmt: Parser[PLocalVariableDecl] =
    typ ~ idndef <~ ";" ^^ { case tpe ~ id => PLocalVariableDecl(id, tpe) }

  /* Operator precedences and associativity taken from
   * http://en.cppreference.com/w/cpp/language/operator_precedence
   */

  lazy val expression: PackratParser[PExpression] = exp15

  lazy val exp15: PackratParser[PExpression] = /* Right associative */
    exp14 ~ ("?" ~> expression <~ ":") ~ exp15 ^^ PConditional |
    exp14

  lazy val exp14: PackratParser[PExpression] = /* Left associative*/
    exp14 ~ ("||" ~> exp13) ^^ POr |
    exp13

  lazy val exp13: PackratParser[PExpression] = /* Left associative*/
    exp13 ~ ("&&" ~> exp9) ^^ PAnd |
    exp9

  lazy val exp9: PackratParser[PExpression] = /* Left associative*/
    exp9 ~ ("==" ~> exp6) ^^ PEquals |
    exp9 ~ ("!=" ~> exp6) ^^ { case lhs ~ rhs => PNot(PEquals(lhs, rhs)) } |
    exp8

  lazy val exp8: PackratParser[PExpression] = /* Left associative*/
    exp8 ~ ("<" ~> exp6) ^^ PLess |
    exp8 ~ ("<=" ~> exp6) ^^ PAtMost |
    exp8 ~ (">" ~> exp6) ^^ PGreater |
    exp8 ~ (">=" ~> exp6) ^^ PAtLeast |
    exp6

  lazy val exp6: PackratParser[PExpression] = /* Left associative */
    exp6 ~ ("+" ~> exp3) ^^ PAdd |
    exp6 ~ ("-" ~> exp3) ^^ PSub |
    exp3

  lazy val exp3: PackratParser[PExpression] = /* Right associative */
    "+" ~> exp3 |
    "-" ~> exp3 ^^ (e => PSub(PIntLit(0), e)) |
    "!" ~> exp3 ^^ PNot |
    exp0

  lazy val exp0: PackratParser[PExpression] =
    "true" ^^ (_ => PTrueLit()) |
    "false" ^^ (_ => PFalseLit()) |
    regex("[0-9]+".r) ^^ (lit => PIntLit(BigInt(lit))) |
    idnuse ~ ("(" ~> expressionList <~ ")") ^^ { case callee ~ args => PFuncApp(callee, args) } |
    idnuse ^^ PIdnExp |
    "(" ~> expression <~ ")"

  lazy val expressionList: Parser[Vector[PExpression]] =
    repsep(expression, ",")

  lazy val typeOrVoid: Parser[PType] =
    "void" ^^ (_ => PVoidType()) |
    typ

  lazy val typ: Parser[PType] =
    "int*" ^^ (_ => PRefType(PIntType())) |
    "int" ^^ (_ => PIntType()) |
    "bool*" ^^ (_ => PRefType(PBoolType())) |
    "bool" ^^ (_ => PBoolType())

  lazy val idndef: Parser[PIdnDef] =
    identifier ^^ PIdnDef

  lazy val idnuse: Parser[PIdnUse] =
    identifier ^^ PIdnUse

  lazy val identifier: Parser[String] =
    "[a-zA-Z][a-zA-Z0-9]*".r into (s => {
      if (reservedWords contains s)
        failure(s"""keyword "$s" found where identifier expected""")
      else
        success(s)
    })
}