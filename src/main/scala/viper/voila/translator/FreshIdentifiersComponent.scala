/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import scala.collection.mutable
import viper.silver.{ast => vpr}

trait FreshIdentifiersComponent { this: PProgramToViperTranslator =>
  protected val identifierCounters: mutable.Map[String, Int] = mutable.Map.empty.withDefaultValue(0)

  def freshIdentifier(baseId: String): String = {
    val counter = identifierCounters(baseId)

    identifierCounters(baseId) += 1

    if (counter == 1) {
      s"$baseId"
    } else {
      s"$baseId$counter"
    }
  }

  def freshLabel(baseId: String): vpr.Label = {
    vpr.Label(
      freshIdentifier(baseId),
      Vector.empty
    )()
  }
}
