/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.voila.frontend._
import viper.silver.{ast => vpr}

trait MainTranslatorComponent { this: PProgramToViperTranslator =>
  val returnVarName = "ret"

  def returnVar(typ: PType): vpr.LocalVar =
    vpr.LocalVar(returnVarName)(typ = translateNonVoid(typ))

  val diamondField: vpr.Field =
    vpr.Field("$diamond", vpr.Int)()

  def diamondLocation(rcvr: vpr.Exp): vpr.FieldAccess =
    vpr.FieldAccess(rcvr, diamondField)()

  def diamondAccess(rcvr: vpr.Exp): vpr.FieldAccessPredicate =
    vpr.FieldAccessPredicate(diamondLocation(rcvr), vpr.FullPerm()())()

  def stepFromField(typ: PType): vpr.Field =
    vpr.Field(s"$$stepFrom_$typ", translateNonVoid(typ))()

  def stepFromLocation(rcvr: vpr.Exp, typ: PType): vpr.FieldAccess =
    vpr.FieldAccess(rcvr, stepFromField(typ))()

  def stepFromAccess(rcvr: vpr.Exp, typ: PType): vpr.FieldAccessPredicate =
    vpr.FieldAccessPredicate(stepFromLocation(rcvr, typ), vpr.FullPerm()())()

  def stepToField(typ: PType): vpr.Field =
    vpr.Field(s"$$stepTo_$typ", translateNonVoid(typ))()

  def stepToLocation(rcvr: vpr.Exp, typ: PType): vpr.FieldAccess =
    vpr.FieldAccess(rcvr, stepToField(typ))()

  def stepToAccess(rcvr: vpr.Exp, typ: PType): vpr.FieldAccessPredicate =
    vpr.FieldAccessPredicate(stepToLocation(rcvr, typ), vpr.FullPerm()())()

  val intSet: vpr.FuncApp =
    vpr.FuncApp.apply("IntSet", Vector.empty)(vpr.NoPosition, vpr.NoInfo, vpr.SetType(vpr.Int), Vector.empty, vpr.NoTrafos)

  val natSet: vpr.FuncApp =
    vpr.FuncApp("NatSet", Vector.empty)(vpr.NoPosition, vpr.NoInfo, vpr.SetType(vpr.Int), Vector.empty, vpr.NoTrafos)

  def tmpVar(typ: PType): vpr.LocalVarDecl =
    vpr.LocalVarDecl(s"tmp_$typ", translateNonVoid(typ))()

  def tmpVars(tree: VoilaTree): Vector[vpr.LocalVarDecl] =
    tree.root.regions map (region => tmpVar(semanticAnalyser.typ(region.state)))

  def translate(tree: VoilaTree): vpr.Program = {
    val members: Vector[vpr.Member] = (
         heapLocations(tree)
      ++ Vector(diamondField)
      ++ tree.root.regions.flatMap(region => {
           val typ = semanticAnalyser.typ(region.state)

           Vector(stepFromField(typ), stepToField(typ))
         }).distinct
      ++ (tree.root.regions flatMap translate)
      ++ (tree.root.predicates map translate)
      ++ (tree.root.procedures map translate)
    )

    val tmpVarDecls = tmpVars(tree)

    val fields = members collect { case f: vpr.Field => f }
    val predicates = members collect { case p: vpr.Predicate => p }
    val functions = members collect { case f: vpr.Function => f }

    val methods =
      members collect { case m: vpr.Method =>
        m.copy(_locals = tmpVarDecls ++ m.locals)(m.pos, m.info)
      }

    vpr.Program(
      domains = Nil,
      fields = fields,
      functions = functions,
      predicates = predicates,
      methods = methods
    )()
  }

  def translate(member: PMember): vpr.Member =
    member match {
      case r: PRegion => translate(r)
      case p: PPredicate => translate(p)
      case p: PProcedure => translate(p)
    }

  def translate(predicate: PPredicate): vpr.Predicate = {
    vpr.Predicate(
      name = predicate.id.name,
      formalArgs = predicate.formalArgs map translate,
      _body = Some(translate(predicate.body))
    )()
  }

  def translate(procedure: PProcedure): vpr.Method = {
    val formalReturns =
      procedure.typ match {
        case PVoidType() => Nil
        case other => Seq(vpr.LocalVarDecl(returnVarName, translateNonVoid(other))())
      }

    val pres = (
         procedure.pres.map(pre => translate(pre.assertion))
      ++ procedure.inters.map(translate)
    )

    val body =
      procedure.body match {
        case Some(statements) => vpr.Seqn(translate(statements))()
        case None => vpr.Inhale(vpr.FalseLit()())()
      }

    vpr.Method(
      name = procedure.id.name,
      formalArgs = procedure.formalArgs map translate,
      formalReturns = formalReturns,
      _pres = pres,
      _posts = procedure.posts map (post => translate(post.assertion)),
      _locals = procedure.locals map translate,
      _body = body
    )()
  }

  def translate(declaration: PFormalArgumentDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translateNonVoid(declaration.typ))()

  def translate(interference: PInterferenceClause): vpr.AnySetContains = {
    /* TODO: Use correct type */
    val lv = vpr.LocalVar(interference.variable.name)(typ = vpr.Int)
    val set = translate(interference.set)

    vpr.AnySetContains(lv, set)()
  }

  def translate(statements: Vector[PStatement]): Vector[vpr.Stmt] = {
    weaveInStabilizationPoints(flattenStatements(statements)) map translateSingleStatement
  }

  def weaveInStabilizationPoints(statements: Vector[PStatement]): Vector[PStatement] = {
    if (statements.lengthCompare(1) != 1) {
      /* No need to stabilise if we have at most one statement */
      statements
    } else {
      statements flatMap {
        case stmt @ (_: PGhostStatement | _: PRuleStatement) => Vector(stmt)
        case call: PProcedureCall if semanticAnalyser.entity(call.procedure).asInstanceOf[ProcedureEntity].declaration.isPrimitiveAtomic => Vector(call)
        case stmt => Vector(stmt, PStabilizationPoint())
      }
    }
  }

  def flattenStatements(statements: Vector[PStatement]): Vector[PStatement] =
    statements flatMap {
      case PBlock(stmts) => flattenStatements(stmts)
      case stmt => Vector(stmt)
    }

  def translateSingleStatement(statement: PStatement): vpr.Stmt = statement match {
    case _: PBlock =>
      sys.error(s"Unexpectedly found a block of statements (should have been flattened): $statement")

    case PSkip() =>
      vpr.Seqn(Vector.empty)()

    case PIf(cond, thn, els) =>
      val vprIf =
        vpr.If(translate(cond), vpr.Seqn(translate(thn))(), vpr.Seqn(translate(els))())()

      surroundWithSectionComments(statement.statementName, vprIf)

    case PWhile(cond, invs, body) =>
      val vprWhile =
        vpr.While(
          cond = translate(cond),
          invs = invs map (inv => translate(inv.assertion)),
          locals = Nil,
          body = vpr.Seqn(translate(body))()
        )()

      surroundWithSectionComments(statement.statementName, vprWhile)

    case PAssign(lhs, rhs) =>
      val vprAssign =
        /* TODO: Use correct type */
        vpr.LocalVarAssign(vpr.LocalVar(lhs.name)(typ = vpr.Int), translate(rhs))()

      surroundWithSectionComments(statement.statementName, vprAssign)

    case read: PHeapRead =>
      val vprRead = translate(read)

      surroundWithSectionComments(statement.statementName, vprRead)

    case write: PHeapWrite =>
      val vprWrite = translate(write)

      surroundWithSectionComments(statement.statementName, vprWrite)

    case stmt @ PPredicateAccess(predicate, arguments) =>
      val vprArguments =
        semanticAnalyser.entity(predicate) match {
          case _: PredicateEntity => arguments map translate
          case _: RegionEntity => arguments.init map translate
        }

      val loc =
        vpr.PredicateAccess(
          args = vprArguments,
          predicateName = predicate.name
        )(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)

      val acc =
        vpr.PredicateAccessPredicate(
          loc = loc,
          perm = vpr.FullPerm()()
        )()

      stmt match {
        case _: PFold => vpr.Fold(acc)()
        case _: PUnfold => vpr.Unfold(acc)()
      }

    case PInhale(assertion) =>
      val inhale = vpr.Inhale(translate(assertion))()

      surroundWithSectionComments(statement.statementName, inhale)

    case PExhale(assertion) =>
      val exhale = vpr.Exhale(translate(assertion))()

      surroundWithSectionComments(statement.statementName, exhale)

    case PProcedureCall(procedureId, arguments, optRhs) =>
      val procedure =
        semanticAnalyser.entity(procedureId).asInstanceOf[ProcedureEntity].declaration

      if (!procedure.isPrimitiveAtomic)
        sys.error("Calling non-atomic procedures is not yet supported.")

      val vprArguments = arguments map translate

      val vprFormalArgs =
        vprArguments.zipWithIndex map { case (a, i) => vpr.LocalVarDecl(s"x$i", a.typ)() }

      val vprFormalReturns =
        optRhs match {
          case Some(rhs) =>
            val typ = translateNonVoid(semanticAnalyser.typ(PIdnExp(rhs)))
            Vector(vpr.LocalVarDecl(rhs.name, typ)())
          case None =>
            Vector.empty
        }

      val vprMethod = /* TODO: Avoid recreating the method here, lookup `procedure` in a cache */
        vpr.Method(
          name = procedure.id.name,
          formalArgs = vprFormalArgs,
          formalReturns = vprFormalReturns,
          _pres = Vector.empty,
          _posts = Vector.empty,
          _locals = Vector.empty,
          _body = vpr.Seqn(Vector.empty)()
        )()

      val vprCall =
        vpr.MethodCall(
          vprMethod,
          vprArguments,
          vprFormalReturns map (_.localVar)
        )()

      surroundWithSectionComments(statement.statementName, vprCall)


    case stmt: PMakeAtomic => translate(stmt)
    case stmt: PUpdateRegion => translate(stmt)

    case _: PStabilizationPoint =>
      vpr.Seqn(Vector.empty)(info = vpr.SimpleInfo(Vector("", "TODO: Stabilise, i.e. havoc regions")))
  }

  def translate(expression: PExpression): vpr.Exp = expression match {
    case PTrueLit() => vpr.TrueLit()()
    case PFalseLit() => vpr.FalseLit()()
    case PIntLit(n) => vpr.IntLit(n)()
    case PEquals(left, right) => vpr.EqCmp(translate(left), translate(right))()
    case PAnd(left, right) => vpr.And(translate(left), translate(right))()
    case POr(left, right) => vpr.Or(translate(left), translate(right))()
    case PNot(operand) => vpr.Not(translate(operand))()
    case PLess(left, right) => vpr.LtCmp(translate(left), translate(right))()
    case PAtMost(left, right) => vpr.LeCmp(translate(left), translate(right))()
    case PGreater(left, right) => vpr.GtCmp(translate(left), translate(right))()
    case PAtLeast(left, right) => vpr.GeCmp(translate(left), translate(right))()
    case PAdd(left, right) => vpr.Add(translate(left), translate(right))()
    case PSub(left, right) => vpr.Sub(translate(left), translate(right))()
    case PConditional(cond, thn, els) => vpr.CondExp(translate(cond), translate(thn), translate(els))()
    case PExplicitSet(elements) => vpr.ExplicitSet(elements map translate)()
    case PIntSet() => intSet
    case PNatSet() => natSet
    case ret: PRet => returnVar(semanticAnalyser.typ(ret))
    case PIdnExp(id) => translateUseOf(id)

    case pointsTo: PPointsTo => translate(pointsTo)
    case guard: PGuardExp => translate(guard)

    case PPredicateExp(id, args) =>
      semanticAnalyser.entity(id) match {
        case _: PredicateEntity =>
          vpr.PredicateAccess(args map translate, id.name)(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)

        case RegionEntity(decl) =>
          translateUseOf(decl, args)

        case other =>
          sys.error(s"Not yet supported: $other")
      }

    case PDiamond(regionId) =>
      diamondAccess(translateUseOf(regionId))

    case PRegionUpdateWitness(regionId, from, to) =>
      val region = semanticAnalyser.usedWithRegion(regionId)
      val vprRegionType = semanticAnalyser.typ(region.state)
      val vprRegionReceiver = translateUseOf(regionId)
      val vprFrom = translate(from)
      val vprTo = translate(to)

      vpr.And(
        vpr.And(
          stepFromAccess(vprRegionReceiver, vprRegionType),
          vpr.EqCmp(
            stepFromLocation(vprRegionReceiver, vprRegionType),
            vprFrom
          )()
        )(),
        vpr.And(
          stepToAccess(vprRegionReceiver, vprRegionType),
          vpr.EqCmp(
            stepToLocation(vprRegionReceiver, vprRegionType),
            vprTo
          )()
        )()
      )()

    case PIrrelevantValue() => sys.error("Not yet supported in all positions: _")
  }

  def translateUseOf(id: PIdnNode): vpr.Exp = {
    semanticAnalyser.entity(id) match {
      case entity: LogicalVariableEntity => translateUseOf(id, entity.declaration)
      case ArgumentEntity(decl) => vpr.LocalVar(id.name)(typ = translateNonVoid(decl.typ))
      case LocalVariableEntity(decl) => vpr.LocalVar(id.name)(typ = translateNonVoid(decl.typ))
    }
  }

  def translate(declaration: PLocalVariableDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translateNonVoid(declaration.typ))()

  def translateNonVoid(typ: PType): vpr.Type = typ match {
    case PIntType() => vpr.Int
    case PBoolType() => vpr.Bool
    case PSetType(elementType) => vpr.SetType(translateNonVoid(elementType))
    case PRefType(_) => vpr.Ref
    case PRegionIdType() => vpr.Ref
    case unsupported@(_: PVoidType | _: PUnknownType) =>
      sys.error(s"Cannot translate type '$unsupported'")
  }
}
