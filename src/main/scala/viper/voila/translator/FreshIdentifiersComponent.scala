/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.mutable
import viper.silver.{ast => vpr}

trait FreshIdentifiersComponent { this: PProgramToViperTranslator =>
  protected var identifierCounters: mutable.Map[String, Int] = mutable.Map.empty.withDefaultValue(0)

  def freshIdentifier(baseId: String): String = {
    identifierCounters(baseId) += 1

    s"$baseId${identifierCounters(baseId)}"
  }

  def freshLabel(baseId: String): vpr.Label = {
    vpr.Label(
      freshIdentifier(baseId),
      Vector.empty
    )()
  }
}
