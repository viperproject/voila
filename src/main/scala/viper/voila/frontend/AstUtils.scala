/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.collect

object AstUtils {
  def extractLogicalVariableBinders(statement: PStatement): Vector[PLogicalVariableBinder] = {
      val collectBinders = collect[Vector, PLogicalVariableBinder] {
        case binder: PLogicalVariableBinder => binder
      }

      val collectRelevantBinders = collect[Vector, Vector[PLogicalVariableBinder]] {
        case PAssert(assertion) => collectBinders(assertion)
        case PExhale(assertion) => collectBinders(assertion)
        case PInhale(assertion) => collectBinders(assertion)
        case foldUnfold: PFoldUnfold => collectBinders(foldUnfold.predicateExp)
      }

    collectRelevantBinders(statement).flatten
  }
}
