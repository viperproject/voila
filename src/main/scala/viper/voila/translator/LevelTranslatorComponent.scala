/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.collect
import viper.silver.{ast => vpr}
import viper.voila.frontend._

trait LevelTranslatorComponent { this: PProgramToViperTranslator =>

  object LevelManager {

    private var currentToken: LevelToken = _

    def clear(): Unit = currentToken = getFreshLevelToken

    private def getFreshLevelToken: LevelToken = LevelToken(declareFreshVariable(vpr.Int, "_levelVar").localVar)
    case class LevelToken private (levelVar: vpr.LocalVar)

    def getCurrentLevelToken: LevelToken = currentToken

    def levelHigherThanOccurringRegionLevels(exp: PExpression): vpr.Exp = {
      val collectedLevels = collectLevels(exp).distinct

      viper.silicon.utils.ast.BigAnd(
        collectedLevels map {l => vpr.GtCmp(currentToken.levelVar, translate(l))()}
      )
    }

    def levelHigherOrEqualToProcedureLevel(procedure: PProcedure): vpr.Exp = {
      val collectedLevels = procedure.pres
        .flatMap{ pre => collectLevels(pre.assertion) }.distinct

      viper.silicon.utils.ast.BigAnd(
        vpr.GeCmp(currentToken.levelVar, vpr.IntLit(0)())() +:
        (collectedLevels map {l => vpr.GtCmp(currentToken.levelVar, translate(l))()})
      )
    }

    def assignLevel(rhs: vpr.Exp): vpr.Stmt = {
      currentToken = getFreshLevelToken
      vpr.LocalVarAssign(currentToken.levelVar, rhs)()
    }

    def assignOldLevel(rhs: LevelToken): vpr.Stmt = {
      currentToken = getFreshLevelToken
      vpr.LocalVarAssign(currentToken.levelVar, rhs.levelVar)()
    }

    def compareToOldLevel(rhs: LevelToken): vpr.Exp =
      vpr.EqCmp(currentToken.levelVar, rhs.levelVar)()

  }

  object AtomicityContextLevelManager {

    var currentAtomicityContextLevels: List[vpr.Exp] = Nil

    def noRecordedRegions: Boolean = currentAtomicityContextLevels.isEmpty

    def registerRegionExp(region: PRegion, args: Vector[vpr.Exp]): vpr.Stmt = {
      val levelVar = declareFreshVariable(vpr.Int, "_levelVar").localVar
      currentAtomicityContextLevels ::= levelVar
      vpr.LocalVarAssign(levelVar, args(1))()
    }

    def removeLastRegionExp(): Unit = {
      currentAtomicityContextLevels = currentAtomicityContextLevels.tail
    }

    def callIsPossible(procedure: PProcedure): vpr.Exp = {
      val collectedLevels = procedure.pres
        .flatMap{ pre => collectLevels(pre.assertion) }.distinct
          .map(translate)

      viper.silicon.utils.ast.BigAnd(
        currentAtomicityContextLevels.flatMap{a =>
          collectedLevels map {l => vpr.GtCmp(a, l)()}
        }
      )
    }

  }

  // TODO: extremely hacky maybe improve with kiama rewriting
  def collectWithPredicateUnfolding[A](exp: PExpression)(func: PartialFunction[PExpression, A]): List[A] = {
    val buffer: collection.mutable.ListBuffer[A] = collection.mutable.ListBuffer.empty

    var visitedExpressions: Set[PExpression] = Set.empty

    def customTranslationScheme: PartialFunction[PExpression, vpr.Exp] = {
      case exp: PPredicateExp if extractablePredicateInstance(exp) && !visitedExpressions.contains(exp) =>
        visitedExpressions += exp
        val translatedBody = translatePredicateBodyWith(exp)(customTranslationScheme)
        translatedBody.getOrElse(vpr.TrueLit()().withSource(exp))

      case exp: PExpression if func.isDefinedAt(exp) && !visitedExpressions.contains(exp) =>
        visitedExpressions += exp
        buffer += func(exp)
        translateWith(exp)(customTranslationScheme)
    }

    translateWith(exp)(customTranslationScheme)
    buffer.toList
  }

  private def collectLevels(exp: PExpression): Vector[PExpression] = {
    val collectAllPredicateExp = collect[Vector, PPredicateExp] { case exp: PPredicateExp => exp }

    collectAllPredicateExp(exp).filter(extractableRegionInstance)
                               .map{getRegionPredicateDetails(_)._2(1)}
  }




  def dependsOnReturnValues(exp: PExpression, method: PProcedure): Boolean = {

    val collectAllUseNames = collect[Set, String]{ case exp: PIdnExp => exp.id.name }
    val useNames = collectAllUseNames(exp)

    method.formalReturns.exists(f => useNames.contains(f.id.name))
  }


}
