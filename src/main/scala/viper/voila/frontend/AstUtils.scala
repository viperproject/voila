/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.collect

object AstUtils {
  private var counter = 0

  def uniqueName(name: String): String = {
    /* TODO: Current approach does not guarantee globally-unique names */

    counter += 1

    s"$$${name}_$counter"
  }

  def extractNamedBinders(from: PAstNode): Vector[PNamedBinder] = {
    val collectBinders = collect[Vector, PNamedBinder] {
      case binder: PNamedBinder => binder
    }

    collectBinders(from)
  }

  def extractNamedBindersFromGhostStatements(statement: PStatement): Vector[PNamedBinder] = {
      val collectBinders =
        collect[Vector, Vector[PNamedBinder]] {
          case PAssert(assertion) => extractNamedBinders(assertion)
          case PExhale(assertion) => extractNamedBinders(assertion)
          case PInhale(assertion) => extractNamedBinders(assertion)
          case foldUnfold: PFoldUnfold => extractNamedBinders(foldUnfold.predicateExp)
        }

    collectBinders(statement).flatten
  }

  /** True iff `exp` matches the variable name bound by `binder`. */
  def isBoundVariable(exp: PExpression, binder: PLogicalVariableBinder): Boolean =
    (exp, binder) match {
      case (PIdnExp(PIdnUse(name)), namedBinder: PNamedBinder) => name == namedBinder.id.name
      case _ => false
    }

}
