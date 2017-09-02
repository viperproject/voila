/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.backends

import java.nio.file.Path
import viper.silver.ast.Program
import viper.silver.frontend.{SilFrontend, SilFrontendConfig, TranslatorState}
import viper.silver.verifier.{AbstractError, Verifier}

class MockViperFrontend extends SilFrontend {
  def createVerifier(fullCmd: _root_.scala.Predef.String): Verifier = ???

  def configureVerifier(args: Seq[String]): SilFrontendConfig = ???

  def translate(silverFile: Path): (Option[Program], Seq[AbstractError]) = {
    _verifier = None
    _state = TranslatorState.Initialized

    reset(silverFile)
    translate()

    (_program, _errors)
  }
}
