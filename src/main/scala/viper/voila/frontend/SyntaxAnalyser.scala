/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import java.util.regex.Pattern
import scala.collection.breakOut
import scala.language.implicitConversions
import org.bitbucket.inkytonik.kiama.parsing.Parsers
import org.bitbucket.inkytonik.kiama.util.Positions

class SyntaxAnalyser(positions: Positions) extends Parsers(positions) {
  private val positionedRewriter = new PositionedRewriter(positions)

  override val whitespace: Parser[String] =
    """(\s|(//.*\s*\n)|/\*(?:.|[\n\r])*?\*/)*""".r

//    """(\s|(//.*\s*\n)|/\*(?s:(.*)?)\*/)*""".r
      // The above regex matches the same whitespace strings as this one:
      //   (\s|(//.*\s*\n)|/\*(?:.|[\n\r])*?\*/)*
      // but (hopefully) avoids potential stack overflows caused by an issue
      // of Oracle's JDK. Note: the issue was reported for Java 6 and 7, it
      // appears to not affect Java 8.
      // See also:
      //   - http://bugs.java.com/bugdatabase/view_bug.do?bug_id=6882582
      //   - https://stackoverflow.com/a/31691056
      //

  val reservedWords: Set[String] = Set(
    "true", "false",
    "int", "bool", "id", "set", "frac", "seq", "tuple", "map",
    "region", "guards", "unique", "manual", "duplicable", "divisible", "interpretation", "abstraction", "actions",
    "predicate", "struct", "procedure", "macro",
    "returns", "interference", "in", "on", "requires", "ensures", "invariant",
    "abstract_atomic", "primitive_atomic", "non_atomic",
    "if", "else", "while", "do", "skip", "new",
    "inhale", "exhale", "assume", "assert", "havoc", "use_region_interpretation", "use_guard_uniqueness", "use",
    "make_atomic", "update_region", "use_atomic", "open_region",
    "true", "false", "null",
    "div", "mod",
    "Set", "Int", "Nat", "union",
    "Seq", "size", "head", "tail", "concat",
    "Tuple",
    "Map", "keys", "vals", "lkup", "upd", "disj",
    "unfolding"
  )

  val reservedPatterns: Set[Pattern] = Set(
    """get\d+""".r.pattern,
    """#option""".r.pattern
  )

  def isReservedWord(word: String): Boolean =
    (reservedWords contains word) || (reservedPatterns exists (_.matcher(word).matches()))

  lazy val program: Parser[PProgram] =
    option.* ~
    (struct | region | predicate | procedure | makro).* ^^ { case options ~ allMembers =>
      val (_macros, _members) = allMembers.partition(_.isInstanceOf[PMacro])
      val macros = _macros.asInstanceOf[Vector[PMacro]]

      val members = positionedRewriter.expand(macros, _members)

      val structs = members collect { case p: PStruct => p }
      val regions = members collect { case p: PRegion => p }
      val predicates = members collect { case p: PPredicate => p }
      val procedures = members collect { case p: PProcedure => p }

      PProgram(options, structs, regions, predicates, procedures)
    }

  lazy val option: Parser[PConfigOption] =
    ("#option" ~> """\w+""".r) ~ ("." ~> """\w+""".r) ~ potentialOptionValue.? ^^ PConfigOption

  lazy val potentialOptionValue: Parser[String] =
    """\w+""".r into (word => {
      if (isReservedWord(word)) failure(s"did not expected keyword '$word' here")
      else success(word)
    })

  lazy val struct: Parser[PStruct] =
    ("struct" ~> idndef) ~
    ("{" ~> (formalArg <~ ";").* <~ "}") ^^ PStruct


  lazy val region: Parser[PRegion] = {

    sealed trait RegionClause
    case class GhostFieldsClause(fields: Vector[PFormalArgumentDecl]) extends RegionClause
    case class GuardClause(guards: Vector[PGuardDecl]) extends RegionClause
    case class InterpretationClause(interp: PExpression) extends RegionClause
    case class StateClause(state: PExpression) extends RegionClause
    case class ActionsClause(actions: Vector[PAction]) extends RegionClause

    lazy val regionClause: Parser[RegionClause] =
      ("ghost_fields" ~> "{" ~> (formalArg <~ ";").* <~ "}") ^^ GhostFieldsClause |
      ("guards" ~> "{" ~> guard.+ <~ "}") ^^ GuardClause |
      ("interpretation" ~> "{" ~> expression <~ "}") ^^ InterpretationClause |
      ("state" ~> "{" ~> expression <~ "}") ^^ StateClause |
      ("actions" ~> "{" ~> action.* <~ "}") ^^ ActionsClause


    lazy val regionClauses: Parser[(
        Option[Vector[PFormalArgumentDecl]],
        Vector[PGuardDecl],
        PExpression,
        PExpression,
        Vector[PAction]
      )] = wrap(regionClause.*, (clauses: Vector[RegionClause]) => {

        val ghostFields = clauses.collect{ case x: GhostFieldsClause => x.fields }
        val guards = clauses.collect{ case x: GuardClause => x.guards }
        val interpretation = clauses.collect{ case x: InterpretationClause => x.interp }
        val state = clauses.collectFirst{ case x: StateClause => x.state }
        val actions = clauses.collectFirst{ case x: ActionsClause => x.actions }

        if (ghostFields.size <= 1 &&
            guards.size <= 1 &&
            interpretation.size == 1 &&
            state.size == 1 &&
            actions.size <= 1
            ) {

          Left((
            ghostFields.headOption,
            guards.headOption.getOrElse(Vector.empty),
            interpretation.head, state.head,
            actions.getOrElse(Vector.empty)
          ))
        } else {
          // exact error message
          var errorMsg = List.empty[String]

          if (ghostFields.size > 1) {
            errorMsg ::= s"expected at most one clause defining ghost fields, but got ${ghostFields.size}"
          }

          if (guards.size > 1) {
            errorMsg ::= s"expected at most one clause defining guards, but got ${guards.size}"
          }

          if (interpretation.size != 1) {
            errorMsg ::= s"expected one interpretation clause, but got ${interpretation.size}"
          }

          if (state.size != 1) {
            errorMsg ::= s"expected one state clause, but got ${state.size}"
          }

          if (actions.size > 1) {
            errorMsg ::= s"expected at most one action clause, but got ${actions.size}"
          }

          Right(errorMsg.mkString("\n"))
        }
      })

    ("region" ~> idndef) ~
    ("(" ~> formalArgsNonEmpty) ~ ((";" ~> formalArgsNonEmpty).? <~ ")") ~
    regionClauses ^^ {
      case id ~ inArgs ~ optOutArgs ~ clauses =>
        val (optGhostFields, guards, interpretation, state, actions) = clauses
        val outArgs = optOutArgs.getOrElse(Vector.empty)

        PRegion(
          id,
          inArgs,
          outArgs,
          guards,
          interpretation,
          state,
          actions,
          optGhostFields.getOrElse(Vector.empty))
    }
  }



  lazy val guard: Parser[PGuardDecl] =
    /* The mandatory region id argument is not Setly declared; e.g. G(int n) actually
     * declares a guard G(id r, int n). Not sure if we want that in the long run.
     */
    guardModifier ~ idndef ~ ("(" ~> formalArgs <~ ")") <~ ";" ^^ {
      case mod ~ id ~ args => mod match {
        case _: PUniqueGuard | _: PDuplicableGuard =>
          PGuardDecl(id, args, mod)
        case _: PDivisibleGuard => ???
          /* TODO: divisible guards with formal arguments are currently not supported */
//          PGuardDecl(id, PFormalArgumentDecl(PIdnDef("perm").at(id),PFracType().at(id)).at(id) +: args, mod)
      }
    } |
    guardModifier ~ idndef <~ ";" ^^ {
      case mod ~ id => mod match {
        case _: PUniqueGuard | _: PDuplicableGuard => PGuardDecl(id, Vector.empty, mod)
        case _: PDivisibleGuard => PGuardDecl(id, Vector(PFormalArgumentDecl(PIdnDef("perm").at(id),PFracType().at(id)).at(id)), mod)
      }
    }

  lazy val guardModifier: Parser[PGuardModifier] =
    "unique" ^^^ PUniqueGuard() |
    "manual" ^^^ PDuplicableGuard() |
    "duplicable" ^^^ PDuplicableGuard() |
    "divisible" ^^^ PDivisibleGuard() |
    success(PUniqueGuard())

  private lazy val guardArg: Parser[PGuardArg] =
    "(" ~> listOfExpressions <~ ")" ^^ PStandardGuardArg |
    "|" ~> expression <~ "|" ^^ PSetGuardArg

  private lazy val guardBasePrefix: Parser[PBaseGuardExp] =
    idnuse ~ guardArg ^^ {
      case guardId ~ args => PBaseGuardExp(guardId, args)
    } |
    idnuse ^^ (guardId => PBaseGuardExp(guardId, PStandardGuardArg(Vector.empty).at(guardId)))

  private lazy val guardPrefix: Parser[Vector[PBaseGuardExp]] =
    rep1sep(guardBasePrefix, "&&")


  lazy val action: Parser[PAction] =
    /* Matches
     *   G(es): e ~> e'
     *   G(es): ?x ~> e'(x)
     *   G(es): e ~> ?x
     *   G(es): ?x ~> ?y
     * where
     *   - G(es) can also just be G
     *   - e/e' are expected to be binder-free
     *   - e/e' are expected to denote a single T (with T the region state's type), or a set of Ts
     */
    (guardPrefix <~ ":") ~
    (binderOrExpression <~ "~>") ~ (binderOrExpression <~ ";") ^^ {
      case guards ~ _from ~ _to =>
        val condition = PTrueLit().at(guards.head)

        var binders = Vector.empty[PNamedBinder]

        def desugareBinders(e: PExpression): PExpression =
          e match {
            case binder: PNamedBinder =>
              binders = binders :+ binder

              PIdnExp(PIdnUse(binder.id.name).at(e)).at(e)
            case _ =>
              e
          }

        val from = desugareBinders(_from)
        val to = desugareBinders(_to)

        postprocessAction(PAction(binders, condition, guards, from, to))
    } |
    /* Matches
     *   ?xs | c(xs) | G(g(xs)): e(xs) ~> e'(xs)
     * where
     *   - the components ?xs and c(xs) are optional
     *   - G(g(xs)) can also just be G
     *   - constraints on e/e' as above
     */
    (listOfBinders <~ "|").? ~
    (expression <~ "|").? ~
    (guardPrefix <~ ":") ~
    (expression <~ "~>") ~ (expression <~ ";") ^^ {
      case optBinders ~ optCondition ~ guards ~ from ~ to =>
        val binders = optBinders.getOrElse(Vector.empty)
        val condition = optCondition.getOrElse(PTrueLit().at(guards.head))

        postprocessAction(PAction(binders, condition, guards, from, to))
    }

  lazy val predicate: Parser[PPredicate] =
    ("predicate" ~> idndef) ~
    ("(" ~> formalArgs <~ ")") ~
    ("{" ~> expression <~ "}").? ^^ {
      case id ~ args ~ body => PPredicate(id, args, body)
    }

  lazy val makro: Parser[PMacro] =
    ("macro" ~> idndef) ~ ("(" ~> repsep(idndef, ",") <~ ")").? ~ typ <~ ";" ^^ PTypeMacro |
    ("macro" ~> idndef) ~ ("(" ~> repsep(idndef, ",") <~ ")").? ~ expression <~ ";" ^^ PExpressionMacro |
    ("macro" ~> idndef) ~ ("(" ~> repsep(idndef, ",") <~ ")") ~ procedureBody ^^ {
      case id ~ args ~ (locals ~ stmts) => PStatementMacro(id, args, locals, stmts)
    }

  lazy val procedure: Parser[PProcedure] =
    (atomicityModifier ~ ("lemma" ^^^ PLemmaModifier(true) | "procedure" ^^^ PLemmaModifier(false))) ~
    idndef ~ ("(" ~> formalArgs <~ ")") ~
    ("returns" ~> ("(" ~> formalArgs <~ ")")).? ~
    interference.* ~
    methodLvl.? ~
    requires.* ~
    ensures .* ~
    procedureBody.? ^^ {
      case mod ~ proc ~ id ~ args ~ optReturns ~ inters ~ lvl ~ pres ~ posts ~ optBraces =>
        val (locals, body) =
          optBraces match {
            case None =>
              /* Abstract method, i.e. braces omitted */
              (Vector.empty, None)
            case Some(l ~ b) =>
              /* Concrete method with at least one statement in the body */
              (l, Some(b))
          }

        val returns =
          optReturns.getOrElse(Vector.empty).map(fa => PFormalReturnDecl(fa.id, fa.typ).at(fa))

        PProcedure(id, args, returns, inters, lvl, pres, posts, locals, body, mod, proc)
    }

  private lazy val procedureBody: Parser[~[Vector[PLocalVariableDecl], PStatement]] =
    ("{" ~> varDeclStmts) ~ (statementsOrSkip <~ "}")

  lazy val statementsOrSkip: Parser[PStatement] =
    statements | success(PSkip())

  lazy val atomicityModifier: Parser[PAtomicityModifier] =
    "abstract_atomic" ^^^ PAbstractAtomic() |
    "primitive_atomic" ^^^ PPrimitiveAtomic() |
    "non_atomic" ^^^ PNonAtomic() |
    "make_atomic" ^^^ PMakeAbstractAtomic() |
    success(PNonAtomic())

  lazy val formalArgsNonEmpty: Parser[Vector[PFormalArgumentDecl]] =
    rep1sep(formalArg, ",")

  lazy val formalArgs: Parser[Vector[PFormalArgumentDecl]] =
    repsep(formalArg, ",")

  lazy val formalArg: Parser[PFormalArgumentDecl] =
    typ ~ idndef ^^ { case tpe ~ id => PFormalArgumentDecl(id, tpe) }

  lazy val methodLvl: Parser[PExpression] =
    "level" ~> expression <~ ";"

  lazy val interference: Parser[PInterferenceClause] =
    "interference" ~> binder ~
    ("in" ~> expression) ~
    (("on" ~> idnuse).? <~ ";") ^^ PInterferenceClause

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
    "fold" ~> predicateExp <~ ";" ^^ PFold |
    "unfold" ~> predicateExp <~ ";" ^^ PUnfold |
    "duplicate" ~> predicateExp <~ ";" ^^ PDuplicateRegion |
    "acquire_guard" ~> guardExp <~ ";" ^^ PAcquireDuplicableGuard |
    "inhale" ~> expression <~ ";" ^^ PInhale |
    "exhale" ~> expression <~ ";" ^^ PExhale |
    "assume" ~> expression <~ ";" ^^ PAssume |
    "assert" ~> expression <~ ";" ^^ PAssert |
    "havoc" ~> idnuse <~ ";" ^^ PHavocVariable |
    "havoc" ~> location <~ ";" ^^ PHavocLocation |
    "use_region_interpretation" ~> predicateExp <~ ";" ^^ PUseRegionInterpretation |
    "use_guard_uniqueness" ~> guardExp <~ ";" ^^ PUseGuardUniqueness |
    "use" ~> procedureCall ^^ PLemmaApplication |
    makeAtomic |
    updateRegion |
    useAtomic |
    openRegion |
    "(" ~> statements <~ ")" <~ ";" |
    procedureCall |
    "fork" ~> procedureCall ^^ PFork |
    "parallel" ~> ("{" ~> repsep(procedureCall, ",") <~ "}" <~ ";") ^^ PParallelCall |
    newStmt |
    idnuse ~ (":=" ~> location) <~ ";" ^^ { case lhs ~ rhs => PHeapRead(lhs, rhs) } |
    location ~ (":=" ~> expression <~ ";") ^^ PHeapWrite |
    idnuse ~ (":=" ~> expression) <~ ";" ^^ PAssign

  lazy val newStmt: Parser[PNewStmt] =
    idnuse ~ (":=" ~> "new" ~> idnuse) ~
      ("(" ~> listOfExpressions <~ ")") ~
      ("with" ~> guardPrefix).? ~
      (";" | ("{" ~> statements <~ "}" <~ ";".?)) ^^ {
        case lhs ~ cnstr ~ args ~ optGuards ~ ";" =>
          PNewStmt(lhs, cnstr, args, optGuards, None)
        case lhs ~ cnstr ~ args ~ optGuards ~ init =>
          PNewStmt(lhs, cnstr, args, optGuards, Some(init.asInstanceOf[PStatement])) // TODO: Avoid cast
      }

  lazy val procedureCall: Parser[PProcedureCall] =
    (repsep(idnuse, ",") <~ ":=").? ~ idnuse ~ ("(" ~> listOfExpressions <~ ")") <~ ";".? ^^ {
      case optRhs ~ proc ~ args => PProcedureCall(proc, args, optRhs.getOrElse(Vector.empty))
    }

  lazy val location: Parser[PLocation] =
    idnexp ~ ("." ~> idnuse) ^^ PLocation

  /* Parses and unrolls a do-while loop, in a way that avoids name clashes but preserves
   * position information.
   */
  private lazy val parseAndUnrollDoWhileLoop: Parser[~[PStatement, PWhile]] =
    parseDoWhileLoop ^^ {
      case tuple @ (invs, body, cond) =>

        val loop: PWhile = {
          val binders = AstUtils.extractNamedBinders(body)

           /* TODO: Current renaming scheme does not guarantee global name-clash freedom */
          val renamings: Map[String, String] =
            binders.map(b => b.id.name -> s"${b.id.name}$$")(breakOut)

          val clonedBody = positionedRewriter.deepcloneAndRename(body, renamings)

          PWhile(cond, invs, clonedBody)
        }

        /* Since the tuple is obtained from a parser (i.e. returned as a `Parser[...]`) its
         * position has been recorded in `this.positions`. We assign this position to the
         * synthesised while-loop node.
         */
        positions.dupPos(tuple, loop)

        new ~(body, loop)
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
    ("using" ~> predicateExp) ~ ("with" ~> rep1sep(guardExp, "&&") <~ ";".?) ~
      ensures .* ~
      ("{" ~> statements <~ "}") ^^ PMakeAtomic

  lazy val updateRegion: Parser[PUpdateRegion] =
    "update_region" ~>
    ("using" ~> predicateExp <~ ";".?) ~
    ("if" ~> expression <~ ";".?).? ~
    ("{" ~> statements <~ "}") ^^ PUpdateRegion

  lazy val useAtomic: Parser[PUseAtomic] =
    "use_atomic" ~>
    ("using" ~> predicateExp) ~ ("with" ~> rep1sep(guardExp, "&&") <~ ";".?) ~
    ("{" ~> statements <~ "}") ^^ PUseAtomic

  lazy val openRegion: Parser[POpenRegion] =
    "open_region" ~>
    ("using" ~> predicateExp <~ ";".?) ~
    ("{" ~> statements <~ "}") ^^ POpenRegion

  lazy val varDeclStmt: Parser[PLocalVariableDecl] =
    typ ~ idndef <~ ";" ^^ { case tpe ~ id => PLocalVariableDecl(id, tpe) }

  lazy val varDeclStmts: Parser[Vector[PLocalVariableDecl]] =
    (typ ~ rep1sep(idndef, ",") <~ ";").* ^^ (decls =>
      decls flatMap { case tpe ~ ids =>
        ids map (id =>
          PLocalVariableDecl(id, positionedRewriter.deepclone(tpe)).range(tpe, id))})

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
    exp60 ~ ("subset" ~> exp50) ^^ PSetSubset | /* Left-associative */
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
                sym match {
                  case "<=" => PAtMost
                  case "<" => PLess
                  case ">=" => PAtLeast
                  case ">" => PGreater
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
    exp50 ~ ("*" ~> exp40) ^^ PMul |
    exp50 ~ ("/" ~> exp40) ^^ PFrac |
    exp50 ~ ("div" ~> exp40) ^^ PDiv |
    exp50 ~ ("mod" ~> exp40) ^^ PMod |
    exp50 ~ ("union" ~> exp40) ^^ PSetUnion |
    exp50 ~ ("concat" ~> exp40) ^^ PSeqConcat |
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
    "_" ^^^ PAnonymousBinder() |
    ("unfolding" ~> predicateExp <~ "in") ~ expression ^^ PUnfolding |
    "1f" ^^^ PFullPerm() |
    "0f" ^^^ PNoPerm() |
    regex("[0-9]+".r) ^^ (lit => PIntLit(BigInt(lit))) |
    setExp0 |
    seqExp0 |
    tupleExp0 |
    mapExp0 |
    applicationLikeExp |
    (location <~ "|->") ~ (binder | exp70) ^^ PPointsTo |
    (idnuse <~ "|=>") ~ ("(" ~> expression) ~ ("," ~> expression <~ ")") ^^ PRegionUpdateWitness |
    idnuse <~ "|=>" <~ "<D>" ^^ PDiamond |
    idnexp |
    "(" ~> expression <~ ")"

  lazy val idnexp: Parser[PIdnExp] =
    idnuse ^^ PIdnExp

  lazy val applicationLikeExp: Parser[PExpression] =
    guardExp |    /* guardExp must come before predicateExp because the latter can ... */
    predicateExp  /* ... be a syntactic prefix of the former */

  lazy val predicateExp: Parser[PPredicateExp] =
    idnuse ~ ("(" ~> listOfBindersOrExpressions <~ ")") ^^ {
      case callee ~ args => PPredicateExp(callee, args)
    }


  lazy val guardExp: Parser[PRegionedGuardExp] =
    idnuse ~ guardArg ~ ("@" ~> idnexp) ^^ {
      case guardId ~ args ~ regionId => PRegionedGuardExp(guardId, regionId, args)
    } |
    (idnuse <~ "@") ~ idnexp ^^ {
      case guardId ~ regionId => PRegionedGuardExp(guardId, regionId, PStandardGuardArg(Vector.empty).at(guardId))
    }

  lazy val setExp0: Parser[PSetExp] =
    setLiteral | setComprehension

  lazy val setLiteral: Parser[PSetExp with PLiteral] =
    "Set" ~> ("<" ~> typ <~ ">").? ~ ("(" ~> listOfExpressions <~ ")") ^^ {
      case typeAnnotation ~ elements => PExplicitSet(elements, typeAnnotation)
    } |
    "Int" ^^^ PIntSet() |
    "Nat" ^^^ PNatSet()

  lazy val setComprehension: Parser[PSetComprehension] =
    "Set" ~> ("<" ~> typ <~ ">").? ~ ("(" ~> binder) ~ ("|" ~> expression) <~ ")" ^^ {
      case typeAnnotation ~ qvar ~ filter => PSetComprehension(qvar, filter, typeAnnotation)
    }

  lazy val seqExp0: Parser[PSeqExp] =
    seqLiteral |
    "size" ~> "(" ~> expression <~ ")" ^^ PSeqSize |
    "head" ~> "(" ~> expression <~ ")" ^^ PSeqHead |
    "tail" ~> "(" ~> expression <~ ")" ^^ PSeqTail

  lazy val seqLiteral: Parser[PExplicitSeq] =
    "Seq" ~> ("<" ~> typ <~ ">").? ~ ("(" ~> listOfExpressions <~ ")") ^^ {
      case typeAnnotation ~ elements => PExplicitSeq(elements, typeAnnotation)
    }

  lazy val tupleExp0: Parser[PTupleExp] =
    tupleLiteral |
    ("get" ~> regex("[0-9]+".r)) ~ ("(" ~> expression <~ ")") ^^ {
      case index ~ expr => PTupleGet(expr, index.toInt)
    }

  lazy val tupleLiteral: Parser[PExplicitTuple] =
    "Tuple" ~>
    ("<" ~> rep1sep(typ, ",") <~ ">").? ~
    ("(" ~> rep1sep(expression, ",") <~ ")") ^^ {
      case typeAnnotations ~ elements =>
        PExplicitTuple(elements, typeAnnotations)
    }

  lazy val mapExp0: Parser[PMapExp] =
    mapLiteral |
    "keys" ~> "(" ~> expression <~ ")" ^^ PMapKeys |
    "vals" ~> "(" ~> expression <~ ")" ^^ PMapValues |
    "lkup" ~> ("(" ~> (expression <~ ",") ~ expression <~ ")") ^^ PMapLookup |
    "disj" ~> ("(" ~> (expression <~ ",") ~ expression <~ ")") ^^ PMapDisjoint |
    "uni" ~> ("(" ~> (expression <~ ",") ~ expression <~ ")") ^^ PMapUnion |
    "upd" ~> ("(" ~> (expression <~ ",") ~ (expression <~ ",") ~ expression <~ ")") ^^ PMapUpdate

  lazy val mapLiteral: Parser[PExplicitMap] =
    "Map" ~>
    ("<" ~> (typ <~ ",") ~ typ <~ ">").? ~
    ("(" ~> repsep((expression <~ ":=") ~ expression, ",") <~ ")") ^^ {
      case typeAnnotation ~ elements => PExplicitMap(elements, typeAnnotation)
    }

  lazy val binder: Parser[PNamedBinder] =
    typ.? ~ ("?" ~> idndef) ^^ { case optType ~ id => PNamedBinder(id, optType) }

  lazy val listOfBinders: Parser[Vector[PNamedBinder]] =
    repsep(binder, ",")

  lazy val listOfExpressions: Parser[Vector[PExpression]] =
    repsep(expression, ",")

  lazy val binderOrExpression: Parser[PExpression] =
    binder | expression

  lazy val listOfBindersOrExpressions: Parser[Vector[PExpression]] =
    repsep(binderOrExpression, ",")

  lazy val typ: PackratParser[PType] =
    "int" ^^^ PIntType() |
    "bool" ^^^ PBoolType() |
    "id" ^^^ PRegionIdType() |
    "frac" ^^^ PFracType() |
    "set" ~> "<" ~> typ <~ ">" ^^ PSetType |
    "seq" ~> "<" ~> typ <~ ">" ^^ PSeqType |
    "tuple" ~> "<" ~> rep1sep(typ, ",") <~ ">" ^^ PTupleType |
    "map" ~> "<" ~> (typ <~ ",") ~ typ <~ ">" ^^ PMapType |
    idnuse ^^ PRefType

  lazy val idndef: Parser[PIdnDef] =
    identifier ^^ PIdnDef

  lazy val idnuse: Parser[PIdnUse] =
    identifier ^^ PIdnUse

  lazy val identifier: Parser[String] =
    "[a-zA-Z_][a-zA-Z0-9_]*".r into (s => {
      if (isReservedWord(s))
        failure(s"""keyword "$s" found where identifier expected""")
      else
        success(s)
    })

  implicit class PositionedPAstNode[N <: PAstNode](node: N) {
    def at(other: PAstNode): N = {
      positions.dupPos(other, node)
    }

    def range(from: PAstNode, to: PAstNode): N = {
      positions.dupRangePos(from, to, node)
    }
  }

  private def postprocessAction(action: PAction): PAction = {
    // Desugares actions with sets of values in from/to position as follows: an action of shape
    //   ?xs | c(xs) | G(g(xs)): S(xs) ~> S'(xs)
    // where S/S' are set-typed expressions, is desugared into
    //   ?xs,?y,?z | c(xs) && y in S(xs) && z in S'(xs) | G(g(xs)): y ~> z
    // If neither from nor to is a set-expressions, nothing is changed.
    def desugareSetExp(binders: Vector[PNamedBinder], condition: PExpression, expToDesugare: PExpression)
                      : (Vector[PNamedBinder], PExpression, PExpression) = {

      expToDesugare match {
        case setExp: PSetExp =>
          val optTypeAnnotation =
            setExp match {
              case e: PExplicitSet => e.typeAnnotation
              case e: PSetComprehension => e.typeAnnotation
              case _ => None
            }

          val binder = PNamedBinder(PIdnDef(AstUtils.uniqueName("from")).at(setExp), optTypeAnnotation).at(setExp)
          val boundVariable = PIdnExp(PIdnUse(binder.id.name).at(setExp)).at(setExp)
          val condition = PSetContains(boundVariable, setExp).at(setExp)

          (binders :+ binder, PAnd(condition, condition).at(setExp), boundVariable)

        case _ => // Nothing to desugare
          (binders, condition, expToDesugare)
      }
    }

    val (binders1, conditions1, desugaredFrom) = desugareSetExp(action.binders, action.condition, action.from)
    val (binders2, conditions2, desugaredTo) = desugareSetExp(binders1, conditions1, action.to)

    sanitizeAction(PAction(binders2, conditions2, action.guards, desugaredFrom, desugaredTo).at(action))
  }

  private def sanitizeAction(action: PAction): PAction = {
    val renamings = (action.binders map { case PNamedBinder(id, _) =>
      id.name -> s"$$_action_${id.name}" /* TODO: Naming convention */
    }).toMap

    positionedRewriter.deepcloneAndRename(action, renamings)
  }

  implicit def parseResultToTuple2[A, B](result: A~B): (A, B) =
    (result._1, result._2)

  implicit def parseResultToTuple2[A, B](result: Option[A~B]): Option[(A, B)] =
    result map (r => (r._1, r._2))

  implicit def parseResultsToTuple2s[A, B](results: Vector[A~B]): Vector[(A, B)] =
    results map (r => (r._1, r._2))
}
