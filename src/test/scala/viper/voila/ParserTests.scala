/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import scala.reflect.{ClassTag, classTag}
import scala.util.{Left, Right}
import org.bitbucket.inkytonik.kiama.util.StringSource
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
  private val `x` = PIdnUse("x")
  private val `y.f` = PLocation(PIdnExp(PIdnUse("y")), PIdnUse("f"))
  private val `bxp` = PIdnExp(PIdnUse("b"))
  private val Emp = Vector.empty

  test("Parse: empty program") {
    val src = ""

    frontend.parse(src) should matchPattern {
      case Right(PProgram(Emp, Emp, Emp, Emp, Emp)) =>
    }
  }

  test("Parse: simple program") {
    val src = "procedure proc() {}"

    val proc =
      PProcedure(PIdnDef("proc"),
                 Emp,
                 Emp,
                 Emp,
                 None,
                 Emp,
                 Emp,
                 Emp,
                 Some(PSkip()),
                 PNonAtomic(),
                 PLemmaModifier(false))

    frontend.parse(src) should matchPattern {
      case Right(PProgram(Emp, Emp, Emp, Emp, Vector(`proc`))) =>
    }
  }

  test("Parser: left associativity") {
    frontend.parseExp("1 + 2 + 3") should matchPattern {
      case PAdd(PAdd(`1`, `2`), `3`) =>
    }
  }

  test("Parser: right associativity") {
    frontend.parseExp("!!+1") should matchPattern {
      case PNot(PNot(`1`)) =>
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
    frontend.parseExp("-x()-1") should matchPattern {
      case PSub(PSub(`0`, PPredicateExp(`x`, Emp)), `1`) =>
    }
  }

  test("Parser: conditionals") {
    frontend.parseExp("b ? true : b ? false : 1 == 2") should matchPattern {
      case PConditional(`bxp`, `true`, PConditional(`bxp`, `false`, PEquals(`1`, `2`))) =>
    }

    frontend.parseExp("b ? b ? false : true : b ? true : false") should matchPattern {
      case PConditional(`bxp`, PConditional(`bxp`, `false`, `true`), PConditional(`bxp`, `true`, `false`)) =>
    }
  }

  test("Parser: assignments") {
    frontend.parseStmt("x := 0;") should matchPattern {
      case PAssign(`x`, `0`) =>
    }

    frontend.parseStmt("y.f := 0;") should matchPattern {
      case PHeapWrite(`y.f`, `0`) =>
    }

    frontend.parseStmt("x := y.f;") should matchPattern {
      case PHeapRead(`x`, `y.f`) =>
    }
  }
}

class TestFrontend extends Frontend {
  private def parseOrFail[T: ClassTag](source: String, parser: syntaxAnalyser.Parser[T]): T = {
    parse(StringSource(source), parser) match {
      case Right(ast) if classTag[T].runtimeClass.isAssignableFrom(ast.getClass) => ast
      case Left(messages) => sys.error(s"Parsing failed: $messages")
      case Right(ast) => sys.error(s"Parsing resulted in unexpected AST node ${ast.getClass.getSimpleName}")
    }
  }

  def parseExp(source: String): PExpression = parseOrFail(source, syntaxAnalyser.expression)
  def parseStmt(source: String): PStatement = parseOrFail(source, syntaxAnalyser.singleStatement)
}
