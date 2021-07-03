/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.backends

import viper.silver

trait Backend[I, O] {
  def start(): Unit
  def handle(input: I): O
  def stop(): Unit
}

trait ViperVerifier extends Backend[silver.ast.Program, silver.verifier.VerificationResult] {

  /** Alias for [[handle]] */
  def verify(program: silver.ast.Program): silver.verifier.VerificationResult = handle(program)
}
