/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.collect

object AstUtils {
  def extractLogicalVariableBinders(statement: PStatement): Vector[PNamedBinder] = {
      val collectBinders = collect[Vector, PNamedBinder] {
        case binder: PNamedBinder => binder
      }

      val collectRelevantBinders = collect[Vector, Vector[PNamedBinder]] {
        case PAssert(assertion) => collectBinders(assertion)
        case PExhale(assertion) => collectBinders(assertion)
        case PInhale(assertion) => collectBinders(assertion)
        case foldUnfold: PFoldUnfold => collectBinders(foldUnfold.predicateExp)
      }

    collectRelevantBinders(statement).flatten
  }
}
