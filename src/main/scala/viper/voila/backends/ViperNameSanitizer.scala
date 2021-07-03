/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.backends

import viper.silicon.decider.AbstractNameSanitizer
import scala.util.matching.Regex

/* TODO: In the long run, there shouldn't be a compile-time dependency on Silicon */

/* TODO: Memoise sanitised names */

class ViperNameSanitizer extends AbstractNameSanitizer {
  val fallback: String = "_"
  val substitutions: Map[Char, Char] = Map.empty

  private val saveChars: String = fallback + "_$$@a-zA-Z" ++ substitutions.values

  val firstCharacters: Regex = s"[$saveChars]".r
  val otherCharacters: Regex = s"[0-9.$saveChars]".r

  val reservedNames: Set[String] = viper.silver.parser.FastParser.keywords
}
