/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import com.typesafe.scalalogging.StrictLogging
import viper.voila.backends.ViperPreamble
import viper.silicon.decider.NameSanitizer
import viper.voila.frontend.{Config, SemanticAnalyser, VoilaTree}
import viper.silver.{ast => vpr}

/* TODO: Reconsider signatures and/or general design */
trait Translator[F, T] {
  def translate(source: F): (T, ErrorBacktranslator)
}

class PProgramToViperTranslator(protected val config: Config,
                                protected val semanticAnalyser: SemanticAnalyser,
                                protected val preamble: ViperPreamble,
                                protected val nameSanitizer: NameSanitizer)
    extends Translator[VoilaTree, vpr.Program]
       with MainTranslatorComponent
       with HeapAccessTranslatorComponent
       with RegionTranslatorComponent
       with RuleTranslatorComponent
       with InterferenceTranslatorComponent
       with StabilizationComponent
       with ActionTranslatorComponent
       with LevelTranslatorComponent
       with CommentsComponent
       with FreshIdentifiersComponent
       with SetComprehensionComponent
       with ErrorReportingComponent
       with StrictLogging
