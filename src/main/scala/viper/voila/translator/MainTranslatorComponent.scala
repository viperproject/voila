/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.breakOut
import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.{collect, collectall}
import viper.silver.{ast => vpr}
import viper.silver.verifier.{errors => vprerr, reasons => vprrea}
import viper.voila.frontend._
import viper.voila.reporting.{FoldError, InsufficientRegionPermissionError, InterferenceError, PreconditionError, UnfoldError}

trait MainTranslatorComponent { this: PProgramToViperTranslator =>

  /*
   * Mutable state
   */

  private var translationIndentation = 0
  private def indent(depth: Int = translationIndentation): String = " " * 2 * depth

  private var _tree: VoilaTree = _
  protected def tree: VoilaTree = _tree

  private var _errorBacktranslator: ErrorBacktranslator = _
  protected def errorBacktranslator: ErrorBacktranslator = _errorBacktranslator

  private var _translatedProcedureStubs: Map[String, vpr.Method] = _
  protected def translatedProcedureStubs: Map[String, vpr.Method] = _translatedProcedureStubs

  /*
   * Immutable state and utility methods
   */

  val diamondField: vpr.Field =
    vpr.Field("$diamond", vpr.Int)()

  def diamondLocation(rcvr: vpr.Exp): vpr.FieldAccess =
    vpr.FieldAccess(rcvr, diamondField)()

  def diamondAccess(rcvr: vpr.Exp): vpr.FieldAccessPredicate =
    vpr.FieldAccessPredicate(diamondLocation(rcvr), vpr.FullPerm()())()

  def stepFromField(typ: PType): vpr.Field =
    vpr.Field(s"$$stepFrom_$typ", translate(typ))()

  def stepFromLocation(rcvr: vpr.Exp, typ: PType): vpr.FieldAccess =
    vpr.FieldAccess(rcvr, stepFromField(typ))()

  def stepFromAccess(rcvr: vpr.Exp, typ: PType): vpr.FieldAccessPredicate =
    vpr.FieldAccessPredicate(stepFromLocation(rcvr, typ), vpr.FullPerm()())()

  def stepToField(typ: PType): vpr.Field =
    vpr.Field(s"$$stepTo_$typ", translate(typ))()

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

  val atomicityContextsDomainName: String = "$AtomicityContexts"

  def atomicityContextsDomain(regions: Vector[PRegion]): vpr.Domain =
    vpr.Domain(
      name = atomicityContextsDomainName,
      functions = regions.map(atomicityContextFunction),
      axioms = Vector.empty,
      typVars = Vector.empty
    )()

  def atomicityContextFunctionName(regionName: String): String =
    s"${regionName}X"

  def atomicityContextFunction(regionId: PIdnNode): vpr.DomainFunc = {
    val region = semanticAnalyser.usedWithRegion(regionId)

    atomicityContextFunction(region)
  }

  def atomicityContextFunction(region: PRegion): vpr.DomainFunc = {
    val vprType = vpr.SetType(regionStateFunction(region).typ)

    vpr.DomainFunc(
      name = atomicityContextFunctionName(region.id.name),
      formalArgs = region.formalInArgs map translate,
      typ = vprType
    )(vpr.NoPosition, vpr.NoInfo, atomicityContextsDomainName, vpr.NoTrafos)
  }

  def localVariableDeclaration(binder: PNamedBinder): vpr.LocalVarDecl = {
    vpr.LocalVarDecl(
      binder.id.name,
      translate(semanticAnalyser.typeOfIdn(binder.id))
    )()
  }

  protected var collectedVariableDeclarations: Vector[vpr.LocalVarDecl] = Vector.empty

  def declareFreshVariable(typ: PType, basename: String): vpr.LocalVarDecl =
    declareFreshVariable(translate(typ), basename)

  def declareFreshVariable(typ: vpr.Type, basename: String): vpr.LocalVarDecl = {
    val decl = vpr.LocalVarDecl(s"$$$basename${collectedVariableDeclarations.length}", typ)()

    collectedVariableDeclarations = collectedVariableDeclarations :+ decl

    decl
  }

  def havocMethodName(typ: vpr.Type): String =
    nameSanitizer.sanitize(s"havoc_$typ")

  /* TODO: Reconsider use of havoc methods:
   *         - Avoid introducing a havoc method for each type in the source program
   *         - Maybe use fresh variables instead? What about loops?
   *         - Rename method?
   */
  def usedVariableHavocs(tree: VoilaTree): Vector[vpr.Method] = {
    val voilaTypes =
      PBoolType() +:
      tree.nodes.collect { case typ: PType => typ }

    val vprTypes = voilaTypes.map(translate).distinct

    vprTypes map (typ =>
      vpr.Method(
        name = havocMethodName(typ),
        /* TODO: Name sanitisation must be done (more) systematically */
        formalArgs = Vector.empty,
        formalReturns = Vector(vpr.LocalVarDecl("$r", typ)()),
        pres = Vector.empty,
        posts = Vector.empty,
        body = Some(vpr.Seqn(Vector.empty, Vector.empty)())
      )()
    )
  }

  def havoc(variable: PIdnUse): vpr.Stmt = {
    havoc(translateUseOf(variable).asInstanceOf[vpr.LocalVar])
  }

  def havoc(variable: vpr.LocalVar): vpr.Stmt = {
    vpr.MethodCall(
      havocMethodName(variable.typ),
      Vector.empty,
      Vector(variable)
    )(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)
  }

  def extractLogicalVariableBindings(assertion: PExpression): Vector[vpr.LocalVarAssign] = {
    val collectBindings =
      collectall[Vector, vpr.LocalVarAssign] {
        case PPointsTo(location, binder: PNamedBinder) =>
          val vprVar = localVariableDeclaration(binder).localVar
          val vprValue = translate(location)

          Vector(vpr.LocalVarAssign(vprVar, vprValue)())

        case predicateExp: PPredicateExp =>
          semanticAnalyser.entity(predicateExp.predicate) match {
            case _: RegionEntity =>
              val (region, inArgs, outArgsAndState) = getRegionPredicateDetails(predicateExp)
              val vprInArgs = inArgs map translate

              outArgsAndState.zipWithIndex.flatMap {
                case (binder: PNamedBinder, index) =>
                  val vprVar = localVariableDeclaration(binder).localVar

                  val vprValue =
                    vpr.FuncApp(
                      regionOutArgumentFunction(region, index),
                      vprInArgs
                    )()

                  val vprAssignment =
                    vpr.LocalVarAssign(
                      vprVar,
                      vprValue
                    )()

                  errorBacktranslator.addErrorTransformer {
                    case e @ vprerr.PreconditionInAppFalse(_, _: vprrea.InsufficientPermission, _)
                         if e causedBy vprValue =>

                      InsufficientRegionPermissionError(predicateExp)
                  }

                  Vector(vprAssignment)

                case _ =>  Vector.empty
              }

            case _ => Vector.empty
          }
      }

    collectBindings(assertion)
  }

  /*
   * Main functionality
   */

  def translate(tree: VoilaTree): (vpr.Program, ErrorBacktranslator) = {
    _tree = tree
    _errorBacktranslator = new DefaultErrorBacktranslator

    analyseSetComprehensions(tree)

    // TODO: tree.root appears to be a costly operation rather than a simple getter - investigate

    _translatedProcedureStubs =
      tree.root.procedures.map(procedure =>
        procedure.id.name -> translateAsStub(procedure)
      )(breakOut)

    val topLevelDeclarations: Vector[vpr.Declaration] = (
         Vector(
            diamondField,
            regionStateTriggerFunctionDomain,
            atomicityContextsDomain(tree.root.regions))
      ++ usedVariableHavocs(tree)
      ++ recordedSetComprehensions.values
      ++ tree.root.regions.flatMap(region => {
            val typ = semanticAnalyser.typ(region.state)

            Vector(stepFromField(typ), stepToField(typ))
         }).distinct
      ++ (tree.root.structs flatMap translate)
      ++ (tree.root.regions flatMap translate)
      ++ (tree.root.predicates map translate)
      ++ (tree.root.procedures map translate)
    )

    val fields = topLevelDeclarations collect { case f: vpr.Field => f }
    val predicates = topLevelDeclarations collect { case p: vpr.Predicate => p }
    val functions = topLevelDeclarations collect { case f: vpr.Function => f }
    val methods = topLevelDeclarations collect { case m: vpr.Method => m }

    val additionalDomainFunctions: Map[String, Vector[vpr.DomainFunc]] =
      topLevelDeclarations
        .collect { case d: vpr.DomainFunc => d }
        .groupBy(_.domainName)
        .withDefaultValue(Vector.empty)

    val additionalDomainAxioms: Map[String, Vector[vpr.DomainAxiom]] =
      topLevelDeclarations
        .collect { case d: vpr.DomainAxiom => d }
        .groupBy(_.domainName)
        .withDefaultValue(Vector.empty)

    val domains =
      topLevelDeclarations
        .collect { case d: vpr.Domain => d }
        .map(domain =>
          domain.copy(
            functions = domain.functions ++ additionalDomainFunctions(domain.name),
            axioms = domain.axioms ++ additionalDomainAxioms(domain.name)
          )(domain.pos, domain.info, domain.errT)
        )

    val vprProgram =
      vpr.Program(
        domains = domains,
        fields = fields,
        functions = functions,
        predicates = predicates,
        methods = methods
      )()

    val backtranslator = _errorBacktranslator

    _tree = null
    _errorBacktranslator = null
    _translatedProcedureStubs = null

    (vprProgram, backtranslator)
  }

  def translate(member: PMember): vpr.Member =
    member match {
      case s: PStruct => translate(s)
      case r: PRegion => translate(r)
      case p: PPredicate => translate(p)
      case p: PProcedure => translate(p)
    }

  def translate(struct: PStruct): Vector[vpr.Field] = {
    struct.fields.map(field => toField(struct, field.id))
  }

  def translate(predicate: PPredicate): vpr.Predicate = {
    vpr.Predicate(
      name = predicate.id.name,
      formalArgs = predicate.formalArgs map translate,
      body = predicate.body.map(translate)
    )()
  }

  def translate(procedure: PProcedure): vpr.Method = {
    assert(collectedVariableDeclarations.isEmpty)

    val vprMethod =
      procedure.atomicity match {
        case PAbstractAtomic() =>
          logger.debug(s"\nTranslating abstract-atomic procedure ${procedure.id.name}")
          translateAbstractlyAtomicProcedure(procedure)
        case PNonAtomic() =>
          logger.debug(s"\nTranslating non-atomic procedure ${procedure.id.name}")
          translateStandardProcedure(procedure)
        case PPrimitiveAtomic() =>
          logger.debug(s"\nTranslating primitive-atomic procedure ${procedure.id.name}")
          translateStandardProcedure(procedure)
    }

    val procedureWideBoundLogicalVariableDeclarations: Vector[vpr.LocalVarDecl] = {
      procedure.body match {
        case Some(body) =>
          AstUtils.extractNamedBindersFromGhostStatements(body).map(localVariableDeclaration)
        case None =>
          Vector.empty
      }
    }

    val bodyWithAdditionalVariableDeclarations: Option[vpr.Seqn] =
      vprMethod.body.map(actualBody =>
        actualBody.copy(
          scopedDecls =
              actualBody.scopedDecls ++
              procedureWideBoundLogicalVariableDeclarations ++
              collectedVariableDeclarations
        )(actualBody.pos, actualBody.info, actualBody.errT))

    collectedVariableDeclarations = Vector.empty

    val bodyToVerify: Option[vpr.Seqn] =
      if (!config.include.supplied || config.include().contains(procedure.id.name))
        bodyWithAdditionalVariableDeclarations
      else
        None

    vprMethod.copy(
      body = bodyToVerify
    )(vprMethod.pos, vprMethod.info, vprMethod.errT)
  }

  def translateAsStub(procedure: PProcedure): vpr.Method = {
    val (vprPres, vprPosts) =
      procedure.atomicity match {
        case PAbstractAtomic() =>
          val pres =
            procedure.pres.map(pre => translate(pre.assertion)) ++
            procedure.inters.map(translate)

          val posts = procedure.posts.map(post => translate(post.assertion))

          (pres, posts)

        case PNonAtomic() | PPrimitiveAtomic() =>
          val pres = procedure.pres.map(pre => translate(pre.assertion))
          val posts = procedure.posts map (post => translate(post.assertion))

          (pres, posts)
      }

    vpr.Method(
      name = procedure.id.name,
      formalArgs = procedure.formalArgs map translate,
      formalReturns = procedure.formalReturns map translate,
      pres = vprPres,
      posts = vprPosts,
      body = None
    )().withSource(procedure)
  }

  def translateAbstractlyAtomicProcedure(procedure: PProcedure): vpr.Method = {
    case class Entry(clause: PInterferenceClause,
                     regionPredicate: PPredicateExp,
                     atomicityContext: vpr.DomainFuncApp)

    val regionInterferenceVariables: Map[PIdnUse, Entry] =
      procedure.inters.map(inter => {
        val regionId = inter.region
        val regionPredicate = semanticAnalyser.usedWithRegionPredicate(regionId)
        val vprAtomicityContext = {
          val (_, regionArguments, _) = getAndTranslateRegionPredicateDetails(regionPredicate)

          vpr.DomainFuncApp(
            atomicityContextFunction(regionId),
            regionArguments,
            Map.empty[vpr.TypeVar, vpr.Type]
          )()
        }

        regionId -> Entry(inter, regionPredicate.asInstanceOf[PPredicateExp], vprAtomicityContext)
      }).toMap

    val vprLocals = procedure.locals.map(translate)

    val vprBody = {
      val vprSaveInferenceSets: Vector[vpr.Stmt] =
        regionInterferenceVariables.map { case (_, entry) =>
          vpr.Inhale(
            vpr.EqCmp(
              entry.atomicityContext,
              translate(entry.clause.set)
            )()
          )()
        }(breakOut)

      val vprMainBody =
        procedure.body match {
          case Some(stmt) => translate(stmt)
          case None => vpr.Inhale(vpr.FalseLit()())()
        }

      vpr.Seqn(vprSaveInferenceSets :+ vprMainBody, vprLocals)()
    }

    val vprStub = translatedProcedureStubs(procedure.id.name)

    vprStub.copy(
      body = Some(vprBody)
    )(vprStub.pos, vprStub.info, vprStub.errT)
  }

  def translateStandardProcedure(procedure: PProcedure): vpr.Method = {
    require(
      procedure.inters.isEmpty,
        s"Expected procedure ${procedure.id} to have no interference clause, "
      + s"but found ${procedure.inters}")

    val vprBody = {
      val mainBody =
        procedure.body match {
          case Some(stmt) => translate(stmt)
          case None => vpr.Inhale(vpr.FalseLit()())()
        }

      vpr.Seqn(Vector(mainBody), procedure.locals map translate)()
    }

    val vprStub = translatedProcedureStubs(procedure.id.name)

    vprStub.copy(
      body = Some(vprBody)
    )(vprStub.pos, vprStub.info, vprStub.errT)
  }

  def translate(declaration: PFormalArgumentDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translate(declaration.typ))()

  def translate(declaration: PFormalReturnDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translate(declaration.typ))()

  def translate(interference: PInterferenceClause): vpr.AnySetContains = {
    val vprSet = translate(interference.set)
    val predicateExp = semanticAnalyser.usedWithRegionPredicate(interference.region)
    val vprRegionState = regionState(predicateExp)

    val vprRegionConstraint =
      vpr.AnySetContains(vprRegionState, vprSet)().withSource(interference)

    errorBacktranslator.addReasonTransformer {
      case e: vprrea.AssertionFalse if e causedBy vprRegionConstraint => InterferenceError(interference)
    }

    vprRegionConstraint
  }

  def translate(statement: PStatement): vpr.Stmt = {
    logger.debug(s"${indent()}${statement.getClass.getSimpleName}")
    statement match {
      case _: PCompoundStatement => translationIndentation += 1
      case _ =>
    }

    if (!semanticAnalyser.isGhost(statement) &&
        semanticAnalyser.atomicity(statement) == AtomicityKind.Nonatomic &&
        semanticAnalyser.expectedAtomicity(statement) == AtomicityKind.Atomic) {

      sys.error( "Unexpectedly found a non-atomic and non-ghost statement " +
                s"(${statement.statementName}) in an atomic context " +
                s"(@${statement.lineColumnPosition})")
    }

    val vprStatement = directlyTranslate(statement)

    def mustHavocAfter(s: PStatement): Boolean = {
      semanticAnalyser.atomicity(s) == AtomicityKind.Nonatomic ||
        (semanticAnalyser.atomicity(s) == AtomicityKind.Atomic &&
         !semanticAnalyser.isGhost(s) &&
         semanticAnalyser.expectedAtomicity(s) == AtomicityKind.Nonatomic)
    }

    val optVprHavoc =
      if (mustHavocAfter(statement)) {
        val alreadyHavoced =
          statement match {
            case PSeqComp(_, second) => mustHavocAfter(second)
            case PIf(_, thn, els) => mustHavocAfter(thn) && els.fold(true)(mustHavocAfter)
            case _: PWhile => false
            case _: PMakeAtomic => false
            case _: PUpdateRegion => false
            case _: PUseAtomic => false
            case _: POpenRegion => false
            case _: PCompoundStatement => ??? /* Forgot about a particular compound statement */
            case _ => false
          }

        if (alreadyHavoced) {
          None
        } else {
          Some(stabilizeRegions(s"after ${statement.statementName}@${statement.lineColumnPosition}"))
        }
      } else {
        None
      }

    statement match {
      case _: PCompoundStatement => translationIndentation -= 1
      case _ =>
    }

    vpr.Seqn(
      vprStatement +: optVprHavoc.toVector,
      Vector.empty
    )()
  }

  protected def directlyTranslate(statement: PStatement): vpr.Stmt = {
    statement match {
      case seqComp: PSeqComp =>
        val vprFirstStmt = translate(seqComp.first)
        val vprSecondStmt = translate(seqComp.second)

        vpr.Seqn(
             Vector(vprFirstStmt)
          ++ Vector(vprSecondStmt),
          Vector.empty
        )()

      case PSkip() =>
        vpr.Seqn(Vector.empty, Vector.empty)(info = vpr.SimpleInfo(Vector("skip;")))

      case PIf(cond, thn, els) =>
        var vprIf =
          vpr.If(
            translate(cond),
            vpr.Seqn(Vector(translate(thn)), Vector.empty)(),
            vpr.Seqn(els.toSeq.map(translate), Vector.empty)()
          )()

        vprIf = vprIf.withSource(statement)

        surroundWithSectionComments(statement.statementName, vprIf)

      case PWhile(cond, invs, body) =>
        var vprWhile =
          vpr.While(
            cond = translate(cond),
            invs = invs map (inv => translate(inv.assertion).withSource(inv, overwrite = true)),
            body = vpr.Seqn(Seq(translate(body)), Vector.empty)()
          )()

        vprWhile = vprWhile.withSource(statement)

        surroundWithSectionComments(statement.statementName, vprWhile)

      case PAssign(lhs, rhs) =>
        var vprAssign =
          vpr.LocalVarAssign(
            vpr.LocalVar(lhs.name)(typ = translate(semanticAnalyser.typeOfIdn(lhs))),
            translate(rhs)
          )()

        vprAssign = vprAssign.withSource(statement)

        surroundWithSectionComments(statement.statementName, vprAssign)

      case read: PHeapRead =>
        val vprRead = translate(read)

        surroundWithSectionComments(statement.statementName, vprRead)

      case write: PHeapWrite =>
        val vprWrite = translate(write)

        surroundWithSectionComments(statement.statementName, vprWrite)

      case foldUnfold: PFoldUnfold with PStatement =>
        val (vprPredicateAccess, optConstraints) = translateUseOf(foldUnfold.predicateExp)

        val optVprCheckConstraints =
          optConstraints.map(vpr.Assert(_)().withSource(statement))

        val vprAssignments = extractLogicalVariableBindings(foldUnfold.predicateExp)

        val vprResult =
          foldUnfold match {
            case _: PFold =>
              val vprFold = vpr.Fold(vprPredicateAccess)().withSource(statement)

              optVprCheckConstraints.fold(vprFold: vpr.Stmt)(vprCheck =>
                vpr.Seqn(
                  Vector(vprFold, vprCheck) ++ vprAssignments,
                  Vector.empty
                )()
              )

            case _: PUnfold =>
              val vprUnfold = vpr.Unfold(vprPredicateAccess)().withSource(statement)

              optVprCheckConstraints.fold(vprUnfold: vpr.Stmt)(vprCheck =>
                vpr.Seqn(
                  vprAssignments ++ Vector(vprCheck, vprUnfold),
                  Vector.empty
                )()
              )
          }

        val ebt = this.errorBacktranslator // TODO: Should not be necessary!!!!!
        optVprCheckConstraints.foreach(vprCheck =>
          errorBacktranslator.addErrorTransformer {
            case err: vprerr.AssertFailed if err causedBy vprCheck =>
              foldUnfold match {
                case fold: PFold => FoldError(fold, ebt.translate(err.reason))
                case unfold: PUnfold => UnfoldError(unfold, ebt.translate(err.reason))
              }
          })

        surroundWithSectionComments(statement.statementName, vprResult)

      case PInhale(assertion) =>
        val vprInhale =
          vpr.Inhale(translate(assertion))().withSource(statement)

        val vprAssignments = extractLogicalVariableBindings(assertion)

        val vprResult =
          vpr.Seqn(
            vprInhale +: vprAssignments,
            Vector.empty
          )()

        surroundWithSectionComments(statement.statementName, vprResult)

      case PExhale(assertion) =>
        val vprExhale =
          vpr.Exhale(translate(assertion))().withSource(statement)

        val vprAssignments = extractLogicalVariableBindings(assertion)

        val vprResult =
          vpr.Seqn(
            vprAssignments :+ vprExhale,
            Vector.empty
          )()

        surroundWithSectionComments(statement.statementName, vprResult)

      case PAssert(assertion) =>
        val vprAssert =
          vpr.Assert(translate(assertion))().withSource(statement)

        val vprAssignments = extractLogicalVariableBindings(assertion)

        val vprResult =
          vpr.Seqn(
            vprAssert +: vprAssignments,
            Vector.empty
          )()

        surroundWithSectionComments(statement.statementName, vprResult)

      case PAssume(assertion) =>
        var assume = vpr.Inhale(translate(assertion))()

        assume = assume.withSource(statement)

        surroundWithSectionComments(statement.statementName, assume)

      case PHavocVariable(variable) =>
        var vprHavoc = havoc(variable)

        vprHavoc = vprHavoc.withSource(statement)

        surroundWithSectionComments(statement.statementName, vprHavoc)

      case PHavocLocation(location) =>
        val vprAcc =
          vpr.FieldAccessPredicate(
            translate(location),
            vpr.FullPerm()()
          )().withSource(statement)

        val vprExhale = vpr.Exhale(vprAcc)()
        val vprInhale = vpr.Inhale(vprAcc)()

        val vprStatement =
          vpr.Seqn(
            Vector(vprExhale, vprInhale),
            Vector.empty
          )()

        surroundWithSectionComments(statement.statementName, vprStatement)

      case PUseRegionInterpretation(regionPredicate) =>
        val (region, vprInArgs, Seq()) = getAndTranslateRegionPredicateDetails(regionPredicate)
        val vprRegionId = vprInArgs.head
        val vprRegionPredicateAccess = regionPredicateAccess(region, vprInArgs)

        val vprUnfoldRegion = vpr.Unfold(vprRegionPredicateAccess)()



        val collectAllGuardExps = collect[Vector, PGuardExp] { case exp: PGuardExp => exp }
        val guardExps = collectAllGuardExps(region.interpretation)

        val vprGuardPredicateAccesses = {
          guardExps foreach (guardExp => {
            assert(
              region.formalInArgs.exists(_.id.name == guardExp.regionId.name),
              "Not yet supported: applying the use-region-interpretation statement to " +
              "a region whose interpretation includes guards whose arguments are not " +
              "directly formal region arguments. " +
              s"In this case: $guardExp from the interpretation of region ${region.id}.")})

          guardExps
            .map(guardExp => semanticAnalyser.entity(guardExp.guard).asInstanceOf[GuardEntity])
            .filter(guardEntity => guardEntity.region == region)
            .map(_.declaration)
            .flatMap(guardDecl =>
              guardDecl.modifier match {
                case PUniqueGuard() => Some(translateUseOf(region, guardDecl, vprRegionId, None))
                case PDuplicableGuard() => None
              })
        }

        val vprPermissionConstraintsForUniqueGuards =
          vprGuardPredicateAccesses map (vprGuardAccess => {
            vpr.Inhale(
              vpr.PermLeCmp(
                vpr.CurrentPerm(vprGuardAccess.loc)(),
                vpr.FullPerm()()
              )()
            )()
          })



        val vprFoldRegion = vpr.Fold(vprRegionPredicateAccess)()

        val result =
          vpr.Seqn(
              vprUnfoldRegion +:
              vprPermissionConstraintsForUniqueGuards :+
              vprFoldRegion,
            Vector.empty
          )().withSource(statement)

        surroundWithSectionComments(statement.statementName, result)

      case use @ PLemmaApplication(call) =>
        // TODO: No need to havoc the frame of this call, which happens by reusing the translation
        //       of regular method calls
        directlyTranslate(call)

      case call @ PProcedureCall(procedureId, arguments, rhs) =>
        val callee =
          semanticAnalyser.entity(procedureId).asInstanceOf[ProcedureEntity].declaration

        val vprArguments = arguments map translate
        val vprReturns = rhs map (id => translateUseOf(id).asInstanceOf[vpr.LocalVar])

        val vprInterferenceChecks: vpr.Stmt =
          callee.atomicity match {
            case PNonAtomic() =>
              vpr.Assert(vpr.TrueLit()())()

            case PPrimitiveAtomic() =>
              vpr.Assert(vpr.TrueLit()())()

            case PAbstractAtomic() =>
              // TODO: See Voila issue #29
              // TODO: Inject code comments at various places

              val vprPreHavocLabel = freshLabel("pre_havoc")

              def generateParentRegionHavockingCode(childRegion: vpr.PredicateAccess): (vpr.Exp, vpr.Seqn) = {
                currentlyOpenRegions match {
                  case Nil =>
                    (vpr.FalseLit()(), vpr.Seqn(Vector.empty, Vector.empty)())

                  case (region, regionArguments, vprPreOpenLabel) :: Nil =>
                    val vprRegionArguments = regionArguments map translate
                    val vprRegionAccess = regionPredicateAccess(region, vprRegionArguments)

                    val vprFold = vpr.Fold(vprRegionAccess)()
                    val vprUnfold = vpr.Unfold(vprRegionAccess)()

                    val vprPreHavocLabel = freshLabel("pre_havoc")

                    val havocParentRegion =
                      havocSingleRegionInstance(region, regionArguments, vprPreHavocLabel, None)

                    val vprCalleeRegionPerms = vpr.CurrentPerm(childRegion)()

                    val vprHavocParentRegionCondition =
                      vpr.PermLtCmp(
                        vpr.LabelledOld(
                          vprCalleeRegionPerms,
                          vprPreOpenLabel.name
                        )(),
                        vprCalleeRegionPerms
                      )()

                    val vprResult =
                      vpr.Seqn(
                        Vector(
                          vprFold,
                          vprPreHavocLabel,
                          havocParentRegion.asSeqn,
                          vprUnfold),
                        Vector.empty
                      )()

                    (vprHavocParentRegionCondition, vprResult)

                  case _ =>
                    sys.error("Multiple nested open regions are not yet supported")
                }
              }

              val vprCheckInterferences =
                callee.inters.map (inter => {
                  val regionPredicate = semanticAnalyser.usedWithRegionPredicate(inter.region)
                  val (region, regionArguments, _) = getRegionPredicateDetails(regionPredicate)
                  val vprRegionArguments = regionArguments map translate

                  val vprRegionPredicateAccess =
                    regionPredicateAccess(region, vprRegionArguments)

                  val havocCalleeRegion =
                    havocSingleRegionInstance(region, regionArguments, vprPreHavocLabel, None)

                  val (vprHavocParentRegionCondition, vprHavocParentRegion) =
                    generateParentRegionHavockingCode(vprRegionPredicateAccess.loc)

                  val vprHavocRegion =
                    vpr.If(
                      vprHavocParentRegionCondition,
                      vprHavocParentRegion,
                      vpr.Seqn(
                        Vector(havocCalleeRegion.exhale, havocCalleeRegion.inhale),
                        Vector.empty
                      )()
                    )()

                  // TODO: See Voila issue #28
//                  val vprUnfoldingToLearnRegionStateInvariants =
//                    vpr.Assert(
//                      vpr.Unfolding(
//                        vprRegionPredicateAccess,
//                        vpr.TrueLit()()
//                      )()
//                    )()

                  val vprCurrentState =
                    vpr.FuncApp(
                      regionStateFunction(region),
                      vprRegionArguments
                    )()

                  val vprInterferenceSet = {
                    val vprFormalsToActuals =
                      callee.formalArgs.map(translate(_).localVar).zip(vprArguments).toMap

                    translate(inter.set).replace(vprFormalsToActuals)
                  }

                  val vprCheckStateUnchanged =
                    vpr.Assert(
                      vpr.AnySetContains(
                        vprCurrentState,
                        vpr.LabelledOld(
                          vprInterferenceSet,
                          vprPreHavocLabel.name
                        )()
                      )()
                    )()

                  errorBacktranslator.addErrorTransformer {
                    case e @ vprerr.PreconditionInAppFalse(_, _: vprrea.InsufficientPermission, _)
                         if e causedBy vprCurrentState =>

                      PreconditionError(call, InsufficientRegionPermissionError(regionPredicate))

                    case e @ vprerr.AssertFailed(_, reason, _)
                         if (e causedBy vprCheckStateUnchanged) &&
                            (reason causedBy vprCheckStateUnchanged.exp) =>

                      PreconditionError(call, InterferenceError(inter))
                  }

                  vpr.Seqn(
                    Vector(
                      vprHavocRegion,
                      havocCalleeRegion.constrainStateViaGuards,
                      havocCalleeRegion.constrainStateViaAtomicityContext,
//                      vprUnfoldingToLearnRegionStateInvariants,
                      vprCheckStateUnchanged),
                    Vector.empty
                  )()
                })

              val vprNonDetChoiceVariable = declareFreshVariable(PBoolType(), "nondet").localVar

              val vprHavocNonDetChoiceVariable = havoc(vprNonDetChoiceVariable)

              val vprNonDetCheckBranch =
                vpr.If(
                  vprNonDetChoiceVariable,
                  vpr.Seqn(
                    vprPreHavocLabel +:
                    vprCheckInterferences :+
                    vpr.Inhale(vpr.FalseLit()())(),
                    Vector.empty
                  )(),
                  vpr.Seqn(Vector.empty, Vector.empty)()
                )()

              vpr.Seqn(
                Vector(vprHavocNonDetChoiceVariable, vprNonDetCheckBranch),
                Vector.empty
              )()
          }

        val vprCall = {
          val vprStub = translatedProcedureStubs(procedureId.name)

          val vprPreCallLabel = freshLabel("pre_call")

          val vprPre =
            vpr.utility.Expressions.instantiateVariables(
              viper.silicon.utils.ast.BigAnd(vprStub.pres),
              vprStub.formalArgs,
              vprArguments)

          val vprPost =
            vpr.utility.Expressions.instantiateVariables(
              viper.silicon.utils.ast.BigAnd(vprStub.posts),
              vprStub.formalArgs ++ vprStub.formalReturns,
              vprArguments ++ vprReturns
            ).transform(
              {
                case old: vpr.Old =>
                  vpr.LabelledOld(old.exp, vprPreCallLabel.name)(old.pos, old.info, old.errT)
              },
              vpr.utility.Rewriter.Traverse.TopDown)

          val vprExhalePres = vpr.Exhale(vprPre)()

          val ebt = this.errorBacktranslator // TODO: Should not be necessary!!!!!
          errorBacktranslator.addErrorTransformer {
            case e: vprerr.ExhaleFailed if e causedBy vprExhalePres =>
              PreconditionError(call, ebt.translate(e.reason))
          }

          val stabilizeFrameRegions =
            stabilizeRegions(s"before ${call.statementName}@${call.lineColumnPosition}")

          val vprHavocTargets = vprReturns map havoc

          val vprInhalePosts = vpr.Inhale(vprPost)()

          vpr.Seqn(
            vprPreCallLabel +:
            vprExhalePres +:
            stabilizeFrameRegions +:
            vprHavocTargets :+
            vprInhalePosts,
            Vector.empty
          )()
        }

        val result =
          vpr.Seqn(
            Vector(vprInterferenceChecks, vprCall),
            Vector.empty
          )()

        surroundWithSectionComments(statement.statementName, result)

      case stmt: PMakeAtomic => translate(stmt)
      case stmt: PUpdateRegion => translate(stmt)
      case stmt: PUseAtomic => translate(stmt)
      case stmt: POpenRegion => translate(stmt)
    }
  }

  def stabilizeRegions(reason: String): vpr.Stmt = {
    stabilizeRegions(tree.root.regions, reason)
  }

  def stabilizeRegions(regions: Vector[PRegion], reason: String): vpr.Stmt = {
    logger.debug(s"${indent()} // Stabilising ${regions.mkString(",")} ($reason)")

    val preHavocLabel = freshLabel("pre_havoc")

    vpr.Seqn(
      preHavocLabel +:
      regions.map(region => havocAllRegionsInstances(region, preHavocLabel).asSeqn),
      Vector.empty
    )()
  }

  def translate(expression: PExpression): vpr.Exp =
    translateWith(expression)(PartialFunction.empty)

  def translateWith(expression: PExpression)
                   (customTranslationScheme: PartialFunction[PExpression, vpr.Exp])
                    : vpr.Exp = {

    def go(expression: PExpression) = translateWith(expression)(customTranslationScheme)

    type VprExpConstructor =
      (vpr.Exp, vpr.Exp) => (vpr.Position, vpr.Info, vpr.ErrorTrafo) => vpr.Exp

    type PolymorphicOperatorTranslationScheme =
      Map[Class[_ <: PBinOp], Map[PType, VprExpConstructor]]

    val polymorphicOperatorTranslationScheme: PolymorphicOperatorTranslationScheme =
      Map(
        classOf[PAdd]     -> Map(PIntType() -> vpr.Add.apply,   PFracType() -> vpr.PermAdd.apply),
        classOf[PSub]     -> Map(PIntType() -> vpr.Sub.apply,   PFracType() -> vpr.PermSub.apply),
        classOf[PMul]     -> Map(PIntType() -> vpr.Mul.apply,   PFracType() -> vpr.PermMul.apply),
        classOf[PLess]    -> Map(PIntType() -> vpr.LtCmp.apply, PFracType() -> vpr.PermLtCmp.apply),
        classOf[PAtMost]  -> Map(PIntType() -> vpr.LeCmp.apply, PFracType() -> vpr.PermLeCmp.apply),
        classOf[PGreater] -> Map(PIntType() -> vpr.GtCmp.apply, PFracType() -> vpr.PermGtCmp.apply),
        classOf[PAtLeast] -> Map(PIntType() -> vpr.GeCmp.apply, PFracType() -> vpr.PermGeCmp.apply))

    def transPoly(op: PBinOp): vpr.Exp = {
      assert(
        semanticAnalyser.typ(op.left) == semanticAnalyser.typ(op.right),
          s"Expected both operands of ${op.formatForUsers} to have the same type, but got "
        + s"${semanticAnalyser.typ(op.left)} and ${semanticAnalyser.typ(op.right)}")

      val vprLeft = go(op.left)
      val vprRight = go(op.right)

      val constructor =
        polymorphicOperatorTranslationScheme(op.getClass)(semanticAnalyser.typ(op.left))

      val vprExp =
        constructor(vprLeft, vprRight)(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos)

      vprExp.withSource(expression)
    }

    val defaultTranslationScheme: PartialFunction[PExpression, vpr.Exp] = {
      case PTrueLit() => vpr.TrueLit()().withSource(expression)
      case PFalseLit() => vpr.FalseLit()().withSource(expression)
      case PNullLit() => vpr.NullLit()().withSource(expression)
      case PIntLit(n) => vpr.IntLit(n)().withSource(expression)
      case PFullPerm() => vpr.FullPerm()().withSource(expression)
      case PNoPerm() => vpr.NoPerm()().withSource(expression)
      case PEquals(left, right) => vpr.EqCmp(go(left), go(right))().withSource(expression)
      case PAnd(left, right) => vpr.And(go(left), go(right))().withSource(expression)
      case POr(left, right) => vpr.Or(go(left), go(right))().withSource(expression)
      case PNot(operand) => vpr.Not(go(operand))().withSource(expression)
      case op: PLess => transPoly(op)
      case op: PAtMost => transPoly(op)
      case op: PGreater => transPoly(op)
      case op: PAtLeast => transPoly(op)
      case op: PAdd => transPoly(op)
      case op: PSub => transPoly(op)
      case op: PMul => transPoly(op)

      case PFrac(left, right) =>
        if (semanticAnalyser.typ(left) == PFracType()) {
          assert(semanticAnalyser.typ(right) == PIntType())

          vpr.PermDiv(go(left), go(right))().withSource(expression)
        } else {
          assert(semanticAnalyser.typ(left) == PIntType())
          assert(semanticAnalyser.typ(right) == PIntType())

          vpr.FractionalPerm(go(left), go(right))().withSource(expression)
        }

      case PMod(left, right) => vpr.Mod(go(left), go(right))().withSource(expression)
      case PDiv(left, right) => vpr.Div(go(left), go(right))().withSource(expression)
      case PConditional(cond, thn, els) => vpr.CondExp(go(cond), go(thn), go(els))().withSource(expression)
      case PExplicitSet(elements, _) => vpr.ExplicitSet(elements map translate)().withSource(expression)
      case PSetContains(element, set) => vpr.AnySetContains(go(element), go(set))().withSource(expression)
      case PExplicitSeq(elements, _) => vpr.ExplicitSeq(elements map translate)().withSource(expression)
      case PSeqSize(seq) => vpr.SeqLength(go(seq))().withSource(expression)
      case PSeqHead(seq) => vpr.SeqIndex(go(seq), vpr.IntLit(0)())().withSource(expression)
      case PSeqTail(seq) => vpr.SeqDrop(go(seq), vpr.IntLit(1)())().withSource(expression)
      case PIntSet() => intSet.withSource(expression)
      case PNatSet() => natSet.withSource(expression)
      case PIdnExp(id) => translateUseOf(id).withSource(expression)

      case comprehension: PSetComprehension =>
        val vprFunction = recordedSetComprehensions(comprehension)
        val freeVariables = semanticAnalyser.freeVariables(comprehension)

        assert(
          vprFunction.formalArgs.length == freeVariables.size,
          s"Cardinality mismatch: ${vprFunction.formalArgs.length} vs ${freeVariables.size}")

        vpr.FuncApp(
          vprFunction,
          freeVariables.map(translateUseOf)(breakOut)
        )()

      case pointsTo: PPointsTo => translate(pointsTo)
      case guard: PGuardExp => translate(guard)

      case PUnfolding(predicate, body) =>
        /* TODO: Rather brittle, improve! */
        val vprPredicate =
          go(predicate) match {
            case vprPredicate: vpr.PredicateAccessPredicate => vprPredicate
            case vpr.And(vprPredicate: vpr.PredicateAccessPredicate, _: vpr.Exp) => vprPredicate
            case other => sys.error(s"Unexpectedly found $other as the translation of $predicate")
          }

        val vprBody = go(body)

        vpr.Unfolding(vprPredicate, vprBody)().withSource(expression)

      case predicateExp: PPredicateExp =>
        val (vprPredicateAccess, optVprConstraints) = translateUseOf(predicateExp)

        optVprConstraints match {
          case Some(vprConstraint) =>
            vpr.And(vprPredicateAccess, vprConstraint)().withSource(predicateExp)
          case None =>
            vprPredicateAccess
        }

      case PDiamond(regionId) =>
        diamondAccess(translateUseOf(regionId))

      case PRegionUpdateWitness(regionId, from, to) =>
        val region = semanticAnalyser.usedWithRegion(regionId)
        val vprRegionType = semanticAnalyser.typ(region.state)
        val vprRegionReceiver = translateUseOf(regionId)
        val vprFrom = go(from)
        val vprTo = go(to)

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

      case binder: PAnonymousBinder =>
        sys.error(
          s"Wildcard arguments ($binder) are not yet supported in this position: " +
          s"${binder.position}. In particular, wildcards are not supported in in-argument position, e.g. " +
           "of region assertions.")

      case binder: PNamedBinder =>
        sys.error(
          s"Logical variable binders ($binder) are not yet supported in this position: ${binder.position}. " +
          "In particular, wildcards are not supported in in-argument position, e.g. of region assertions.")
    }

    customTranslationScheme.applyOrElse(expression, defaultTranslationScheme)
  }

  def translateUseOf(id: PIdnNode): vpr.Exp = {
    semanticAnalyser.entity(id) match {
      case entity: LogicalVariableEntity => translateUseOf(id, entity.declaration)
      case FormalArgumentEntity(decl) => vpr.LocalVar(id.name)(typ = translate(decl.typ))
      case FormalReturnEntity(decl) => vpr.LocalVar(id.name)(typ = translate(decl.typ))
      case LocalVariableEntity(decl) => vpr.LocalVar(id.name)(typ = translate(decl.typ))
    }
  }

  def translateUseOf(id: PIdnNode, binder: PNamedBinder): vpr.Exp = {
    semanticAnalyser.boundBy(binder) match {
      case   PAction2(_, `binder`, _)
           | PAction3(_, `binder`, _, _)
           | PSetComprehension(`binder`, _, _) =>

        val vprType = translate(semanticAnalyser.typeOfLogicalVariable(binder))

        vpr.LocalVar(id.name)(typ = vprType)

      case PPointsTo(_, `binder`) => translateAsHeapAccess(id, binder)
      case PPredicateExp(_, args) if args.exists(_ eq binder) => translateAsHeapAccess(id, binder)
      case PInterferenceClause(`binder`, _, _) => translateAsHeapAccess(id, binder)
    }
  }

  def translate(declaration: PLocalVariableDecl): vpr.LocalVarDecl =
    vpr.LocalVarDecl(declaration.id.name, translate(declaration.typ))()

  def translate(typ: PType): vpr.Type = typ match {
    case PIntType() => vpr.Int
    case PBoolType() => vpr.Bool
    case PFracType() => vpr.Perm
    case PSetType(elementType) => vpr.SetType(translate(elementType))
    case PSeqType(elementType) => vpr.SeqType(translate(elementType))
    case PRefType(_) => vpr.Ref
    case PRegionIdType() => vpr.Ref
    case unsupported@(_: PUnknownType) =>
      sys.error(s"Cannot translate type '$unsupported'")
  }
}
