/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.backends

import viper.silver.ast._

class ViperPreamble(preamble: Program) {

  object sets {
    val int: FuncApp = FuncApp(preamble.findFunction("IntSet"), Vector.empty)()
    val nat: FuncApp = FuncApp(preamble.findFunction("NatSet"), Vector.empty)()
  }

  object pairs {
    val domain: Domain = preamble.findDomain("Pair")

    val pair: DomainFunc = preamble.findDomainFunction("pair")
    val first: DomainFunc = preamble.findDomainFunction("fst")
    val second: DomainFunc = preamble.findDomainFunction("snd")

    def typeVarMap(t1: Type, t2: Type) = Map(domain.typVars(0) -> t1, domain.typVars(1) -> t2)
  }

  object maps {
    val domain: Domain = preamble.findDomain("Map")

    val keys: DomainFunc = preamble.findDomainFunction("Map_keys")
    val cardinality: DomainFunc = preamble.findDomainFunction("Map_card")
    val lookup: DomainFunc = preamble.findDomainFunction("Map_lookup")
    val values: DomainFunc = preamble.findDomainFunction("Map_values")
    val empty: DomainFunc = preamble.findDomainFunction("Map_empty")
    val build: DomainFunc = preamble.findDomainFunction("Map_build")
    val equal: DomainFunc = preamble.findDomainFunction("Map_equal")
    val disjoint: DomainFunc = preamble.findDomainFunction("Map_disjoint")
    val union: DomainFunc = preamble.findDomainFunction("Map_union")

    def typeVarMap(t1: Type, t2: Type) = Map(domain.typVars(0) -> t1, domain.typVars(1) -> t2)
  }
}