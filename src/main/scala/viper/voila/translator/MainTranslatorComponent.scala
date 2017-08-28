/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.breakOut
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
    vpr.FuncApp.apply(
      "IntSet",
      Vector.empty
    )(vpr.NoPosition, vpr.NoInfo, vpr.SetType(vpr.Int), Vector.empty, vpr.NoTrafos)

  val natSet: vpr.FuncApp =
    vpr.FuncApp(
      "NatSet",
      Vector.empty
    )(vpr.NoPosition, vpr.NoInfo, vpr.SetType(vpr.Int), Vector.empty, vpr.NoTrafos)

  def temporaryVariable(typ: PType): vpr.LocalVarDecl =
    vpr.LocalVarDecl(s"$$tmp_$typ", translateNonVoid(typ))()

  def atomicityContextVariable(regionId: PIdnNode): vpr.LocalVarDecl = {
    val region = semanticAnalyser.usedWithRegion(regionId)
    val vprType = vpr.SetType(regionStateFunction(region).typ)

    vpr.LocalVarDecl(s"$$${regionId.name}X", vprType)()
  }

  def tmpVars(tree: VoilaTree): Vector[vpr.LocalVarDecl] =
    tree.root.regions.map(region => temporaryVariable(semanticAnalyser.typ(region.state))).distinct

  def usedHavocs(tree: VoilaTree): Vector[vpr.Method] = {
    tree.nodes.collect {
      case PHavoc(variable) =>
        val vprTyp = translateNonVoid(semanticAnalyser.typ(PIdnExp(variable)))

        vpr.Method(
          name = s"havoc_$vprTyp",
          formalArgs = Vector.empty,
          formalReturns = Vector(vpr.LocalVarDecl("$r", vprTyp)()),
          pres = Vector.empty,
          posts = Vector.empty,
          body = vpr.Seqn(Vector.empty, Vector.empty)()
        )()
    }.distinct
  }

  def havoc(variable: PIdnUse): vpr.Stmt = {
    val vprTyp = translateNonVoid(semanticAnalyser.typ(PIdnExp(variable)))

    vpr.MethodCall(
      s"havoc_$vprTyp",
      Vector.empty,
      Vector(translateUseOf(variable).asInstanceOf[vpr.LocalVar])
    )(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)
  }

  private var translationIndentation = 0

  private def indent(depth: Int = translationIndentation): String = " " * 2 * depth

  def translate(tree: VoilaTree): vpr.Program = {
    val members: Vector[vpr.Member] = (
         heapLocations(tree)
      ++ Vector(diamondField)
      ++ usedHavocs(tree)
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
        val bodyWithAdditionalLocalVariables =
          m.body.copy(
            scopedDecls = tmpVarDecls ++ m.body.scopedDecls
          )(m.body.pos, m.body.info, m.body.errT)

        m.copy(body = bodyWithAdditionalLocalVariables)(m.pos, m.info, m.errT)
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
      body = predicate.body.map(translate)
    )()
  }

  def translate(procedure: PProcedure): vpr.Method = {
    procedure.atomicity match {
      case PAbstractAtomic() =>
        logger.debug(s"\nTranslating abstract-atomic procedure ${procedure.id.name}")
        translateAbstractlyAtomicProcedure(procedure)
      case PNotAtomic() =>
        logger.debug(s"\nTranslating non-atomic procedure ${procedure.id.name}")
        translateStandardProcedure(procedure)
      case PPrimitiveAtomic() =>
        logger.debug(s"\nTranslating primitive-atomic procedure ${procedure.id.name}")
        translateStandardProcedure(procedure)
    }
  }

  def translateAbstractlyAtomicProcedure(procedure: PProcedure): vpr.Method = {
    case class Entry(clause: PInterferenceClause,
                     region: PRegion,
                     atomicityContextVar: vpr.LocalVarDecl)

    val formalReturns =
      procedure.typ match {
        case PVoidType() => Nil
        case other => Seq(vpr.LocalVarDecl(returnVarName, translateNonVoid(other))())
      }

    val regionInterferenceVariables: Map[PIdnUse, Entry] =
      procedure.inters.map(inter => {
        val regionId = inter.region
        val region = semanticAnalyser.usedWithRegion(regionId)
        val vprVar = atomicityContextVariable(regionId)

        regionId -> Entry(inter, region, vprVar)
      }).toMap

    val vprLocals = (
         procedure.locals.map(translate)
      ++ regionInterferenceVariables.values.map(entry =>
           vpr.LocalVarDecl(entry.atomicityContextVar.name, entry.atomicityContextVar.typ)()
         )
    )

    val vprPres = (
         procedure.pres.map(pre => translate(pre.assertion))
      ++ procedure.inters.map(translate)
    )

    val vprPosts = procedure.posts.map(post => translate(post.assertion))

    val vprBody = {
      val vprSaveInferenceSets: Vector[vpr.Stmt] =
        regionInterferenceVariables.map { case (_, entry) =>
          vpr.LocalVarAssign(
            entry.atomicityContextVar.localVar,
            translate(entry.clause.set)
          )()
        }(breakOut)

      val vprMainBody =
        procedure.body match {
          case Some(stmt) => translate(stmt)
          case None => vpr.Inhale(vpr.FalseLit()())()
        }

      vpr.Seqn(vprSaveInferenceSets :+ vprMainBody, vprLocals)()
    }

    vpr.Method(
      name = procedure.id.name,
      formalArgs = procedure.formalArgs map translate,
      formalReturns = formalReturns,
      pres = vprPres,
      posts = vprPosts,
      body = vprBody
    )()
  }

  def translateStandardProcedure(procedure: PProcedure): vpr.Method = {
    require(
      procedure.inters.isEmpty,
        s"Expected procedure ${procedure.id} to have no interference clause, "
      + s"but found ${procedure.inters}")

    val formalReturns =
      procedure.typ match {
        case PVoidType() => Vector.empty
        case other => Vector(vpr.LocalVarDecl(returnVarName, translateNonVoid(other))())
      }

    val pres = procedure.pres.map(pre => translate(pre.assertion))

    val body = {
      val mainBody =
        procedure.body match {
          case Some(stmt) => translate(stmt)
          case None => vpr.Inhale(vpr.FalseLit()())()
        }

      vpr.Seqn(Vector(mainBody), procedure.locals map translate)()
    }

    vpr.Method(
      name = procedure.id.name,
      formalArgs = procedure.formalArgs map translate,
      formalReturns = formalReturns,
      pres = pres,
      posts = procedure.posts map (post => translate(post.assertion)),
      body = body
    )()
  }

  def translate(declaration: PFormalArgumentDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translateNonVoid(declaration.typ))()

  def translate(interference: PInterferenceClause): vpr.AnySetContains = {
    val vprSet = translate(interference.set)
    val predicateExp = semanticAnalyser.usedWithRegionPredicate(interference.region)
    val vprRegionState = regionState(predicateExp)

    vpr.AnySetContains(vprRegionState, vprSet)()
  }

  def translate(statement: PStatement): vpr.Stmt = {
    logger.debug(s"${indent()}${statement.getClass.getSimpleName}")
    statement match {
      case _: PCompoundStatement => translationIndentation += 1
      case _ =>
    }

    val vprStatement =
      statement match {
        case seqComp: PSeqComp =>
          val (firstStabilisation, secondStabilisation) = stabiliseAtSeqComp(seqComp)

          val vprFirstStmt = translate(seqComp.first)

          if (firstStabilisation.isDefined)
            logger.debug(s"${indent()}// Stabilise (havoc regions)")

          val vprSecondStmt = translate(seqComp.second)

          if (secondStabilisation.isDefined)
            logger.debug(s"${indent()}// Stabilise (havoc regions)")

          vpr.Seqn(
               Vector(vprFirstStmt)
            ++ firstStabilisation
            ++ Vector(vprSecondStmt)
            ++ secondStabilisation,
            Vector.empty
          )()

        case PSkip() =>
          vpr.Seqn(Vector.empty, Vector.empty)()

        case PIf(cond, thn, els) =>
          val vprIf =
            vpr.If(
              translate(cond),
              vpr.Seqn(Vector(translate(thn)), Vector.empty)(),
              vpr.Seqn(els.toSeq.map(translate), Vector.empty)()
            )()

          surroundWithSectionComments(statement.statementName, vprIf)

        case PWhile(cond, invs, body) =>
          val vprWhile =
            vpr.While(
              cond = translate(cond),
              invs = invs map (inv => translate(inv.assertion)),
              body = vpr.Seqn(Seq(translate(body)), Vector.empty)()
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

        case PHavoc(variable) =>
          val vprHavoc = havoc(variable)

          surroundWithSectionComments(statement.statementName, vprHavoc)

        case PProcedureCall(procedureId, arguments, optRhs) =>
          val procedure =
            semanticAnalyser.entity(procedureId).asInstanceOf[ProcedureEntity].declaration

          if (procedure.atomicity == PNotAtomic())
            sys.error("Calling non-atomic procedures is not yet supported.")

          val vprArguments = arguments map translate

          val vprFormalReturns =
            optRhs match {
              case Some(rhs) =>
                val typ = translateNonVoid(semanticAnalyser.typ(PIdnExp(rhs)))
                Vector(vpr.LocalVarDecl(rhs.name, typ)())
              case None =>
                Vector.empty
            }

          val vprCall =
            vpr.MethodCall(
              procedure.id.name,
              vprArguments,
              vprFormalReturns map (_.localVar)
            )(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)

          surroundWithSectionComments(statement.statementName, vprCall)

        case stmt: PMakeAtomic => translate(stmt)
        case stmt: PUpdateRegion => translate(stmt)
        case stmt: PUseAtomic => translate(stmt)
        case stmt: POpenRegion => translate(stmt)
      }

    statement match {
      case _: PCompoundStatement => translationIndentation -= 1
      case _ =>
    }

    vprStatement
  }

  def stabiliseAtSeqComp(stmt: PSeqComp): (Option[vpr.Stmt], Option[vpr.Stmt]) = {
    val areBothConcrete = (   !semanticAnalyser.isGhost(stmt.first)
                           && !semanticAnalyser.isGhost(stmt.second))

    val isFirstSeqComp = stmt.first.isInstanceOf[PSeqComp]
    val isSecondSeqComp = stmt.second.isInstanceOf[PSeqComp]

    val stabiliseAfterFirst =
      if (areBothConcrete && !isFirstSeqComp) Some(stabiliseAfter(stmt.first))
      else None

    val stabiliseAfterSecond =
      if (areBothConcrete && !isSecondSeqComp) Some(stabiliseAfter(stmt.second))
      else None

    (stabiliseAfterFirst, stabiliseAfterSecond)
  }

  def stabiliseAfter(statement: PStatement): vpr.Stmt = {
    val interference = semanticAnalyser.interferenceSpecifications(statement).head

    val makeAtomic = semanticAnalyser.enclosingMakeAtomic(statement)

    val (region, regionArgs, None) =
      getRegionPredicateDetails(makeAtomic.regionPredicate)

    val havoc = havocRegion(region, regionArgs)

    vpr.Seqn(Vector(havoc), Vector.empty)(info = vpr.SimpleInfo(Vector("TODO: Stabilise all regions")))
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
    case PExplicitSet(elements, _) => vpr.ExplicitSet(elements map translate)()
    case PSetContains(element, set) => vpr.AnySetContains(translate(element), translate(set))()
    case PIntSet() => intSet
    case PNatSet() => natSet
    case ret: PRet => returnVar(semanticAnalyser.typ(ret))
    case PIdnExp(id) => translateUseOf(id)

    case pointsTo: PPointsTo => translate(pointsTo)
    case guard: PGuardExp => translate(guard)

    case predicateExp @ PPredicateExp(id, args) =>
      semanticAnalyser.entity(id) match {
        case _: PredicateEntity =>
          vpr.PredicateAccess(args map translate, id.name)(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)

        case _: RegionEntity =>
          translateUseOf(predicateExp)

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

    case PIrrelevantValue() =>
      sys.error("Wildcard arguments \"_\" are not yet supported in arbitrary positions.")

    case _: PLogicalVariableBinder =>
      sys.error("Logical variable binders are not yet supported in arbitrary positions.")
  }

  def translateUseOf(id: PIdnNode): vpr.Exp = {
    semanticAnalyser.entity(id) match {
      case entity: LogicalVariableEntity => translateUseOf(id, entity.declaration)
      case ArgumentEntity(decl) => vpr.LocalVar(id.name)(typ = translateNonVoid(decl.typ))
      case LocalVariableEntity(decl) => vpr.LocalVar(id.name)(typ = translateNonVoid(decl.typ))
    }
  }

  def translateUseOf(id: PIdnNode, declaration: PLogicalVariableBinder): vpr.Exp = {
    semanticAnalyser.boundBy(declaration) match {
      case PAction(_, `declaration`, _) =>
        val vprType = translateNonVoid(semanticAnalyser.typeOfLogicalVariable(declaration))

        vpr.LocalVar(id.name)(typ = vprType)

      case _ =>
        translateAsHeapAccess(id, declaration)
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
