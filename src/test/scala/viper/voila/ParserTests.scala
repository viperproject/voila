/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import scala.reflect.{ClassTag, classTag}
import scala.util.{Left, Right}
import org.scalatest.{FunSuite, Matchers}
import viper.voila.frontend._

class ParserTests extends FunSuite with Matchers {
  private val frontend = new TestFrontend()

  private val `0` = PIntLit(BigInt(0))
  private val `1` = PIntLit(BigInt(1))
  private val `2` = PIntLit(BigInt(2))
  private val `3` = PIntLit(BigInt(3))
  private val `true` = PTrueLit()
  private val `false` = PFalseLit()
  private val `f` = PIdn(PIdnUse("f"))
  private val Emp = Vector.empty

  test("Parse: empty program") {
    val src = ""

    frontend.parse(src) should matchPattern {
      case Right(PProgram(Seq())) =>
    }
  }

  test("Parse: simple program") {
    val src = "void proc() {}"

    val proc =
      PProcedure(PIdnDef("proc"),
                 Emp,
                 PVoidType(),
                 Emp)

    frontend.parse(src) should matchPattern {
      case Right(PProgram(Seq(`proc`))) =>
    }
  }

  test("Parser: left associativity") {
    frontend.parseExp("1 + 2 + 3") should matchPattern {
      case PAdd(PAdd(`1`, `2`), `3`) =>
    }

    frontend.parseExp("f()()()") should matchPattern {
      case PFuncApp(PFuncApp(PFuncApp(`f`, Emp), Emp), Emp) =>
    }
  }

  test("Parser: right associativity") {
    frontend.parseExp("-+!true") should matchPattern {
      case PUnaryMinus(PUnaryPlus(PNot(`true`))) =>
    }
  }

  test("Parser: precedence") {
    frontend.parseExp("1 + 2 == 3 - 0") should matchPattern {
      case PEquals(PAdd(`1`, `2`), PSub(`3`, `0`)) =>
    }

    frontend.parseExp("false || true && 1 + 1 == 2 || false") should matchPattern {
      case POr(POr(`false`, PAnd(`true`, PEquals(PAdd(`1`, `1`), `2`))), `false`) =>
    }
  }

  test("Parser: associativity and precedence") {
    frontend.parseExp("-f()()-1") should matchPattern {
      case PSub(PUnaryMinus(PFuncApp(PFuncApp(`f`, Emp), Emp)), `1`) =>
    }
  }

  test("Parser: conditionals") {
    frontend.parseExp("f ? true : f ? false : 1 == 2") should matchPattern {
      case PConditional(`f`, `true`, PConditional(`f`, `false`, PEquals(`1`, `2`))) =>
    }

    frontend.parseExp("f ? f ? false : true : f ? true : false") should matchPattern {
      case PConditional(`f`, PConditional(`f`, `false`, `true`), PConditional(`f`, `true`, `false`)) =>
    }
  }

  test("Parser: assignments") {
    frontend.parseStmt("[x] := 0;") should matchPattern {
      case PHeapWrite(PIdnUse("x"), `0`) =>
    }

    frontend.parseStmt("x := 0;") should matchPattern {
      case PAssign(PIdnUse("x"), `0`) =>
    }
  }
}

class TestFrontend extends Frontend {
  private def parseOrFail[T: ClassTag](source: String, parser: syntaxAnalyser.Parser[T]): T = {
    parse(source, parser) match {
      case Right(ast) if classTag[T].runtimeClass.isAssignableFrom(ast.getClass) => ast
      case Left(messages) => sys.error(s"Parsing failed: $messages")
      case Right(ast) => sys.error(s"Parsing resulted in unexpected AST node ${ast.getClass.getSimpleName}")
    }
  }

  def parseExp(source: String): PExpression = parseOrFail(source, syntaxAnalyser.expression)
  def parseStmt(source: String): PStatement = parseOrFail(source, syntaxAnalyser.statement)
}
