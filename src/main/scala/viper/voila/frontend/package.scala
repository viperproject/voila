/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import org.bitbucket.inkytonik.kiama.relation.Tree

package object frontend {
  type VoilaTree = Tree[PAstNode, PProgram]
}
