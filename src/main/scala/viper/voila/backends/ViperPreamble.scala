/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.backends

import viper.silver.ast._

import scala.collection.mutable

class ViperPreamble(preamble: Program) {

  def generatedDomains: Seq[Domain] =
    tuples.generatedDomains

  object sets {
    val int: FuncApp = FuncApp(preamble.findFunction("IntSet"), Vector.empty)()
    val nat: FuncApp = FuncApp(preamble.findFunction("NatSet"), Vector.empty)()
  }

  object tuples {
    private var _generatedDomains: List[Domain] = List.empty
    private val domains: mutable.Map[Int, Domain] = mutable.Map.empty
    private val constructors: mutable.Map[Int, DomainFunc] = mutable.Map.empty
    private val getters: mutable.Map[(Int,Int), DomainFunc] = mutable.Map.empty

    def generatedDomains: List[Domain] = _generatedDomains

    private def addNPairDomain(arity: Int): Unit = {
      val domainName = s"Tuple$arity"

      val typeVars = 0.until(arity) map (ix => TypeVar(s"T$ix"))
      val decls = 0.until(arity) map (ix => LocalVarDecl(s"t$ix", typeVars(ix))())
      val vars = decls map (_.localVar)
      val typVarMap = typeVars.zip(typeVars).toMap

      val domainTyp = DomainType(domainName, typVarMap)(typeVars)
      val domainTypVar = TypeVar("p1")
      val domainDecl = LocalVarDecl("p", domainTyp)()
      val domainVar = domainDecl.localVar

      val tupleFunc = DomainFunc(s"tuple$arity",decls, domainTyp)(domainName = domainName)
      val getFuncs = 0.until(arity) map (ix =>
        DomainFunc(s"get${ix}of${arity}", Seq(domainDecl), typeVars(ix))(domainName = domainName)
      )

      val getOverTupleAxiom = {

        val nPairApp = DomainFuncApp(tupleFunc, vars, typVarMap)()
        val eqs = 0.until(arity) map {ix =>
          EqCmp(
            DomainFuncApp(
              getFuncs(ix),
              Seq(nPairApp),
              typVarMap
            )(),
            vars(ix)
          )()
        }

        DomainAxiom(
          name = s"getter_over_tuple$arity",
          exp = Forall(
            decls,
            Seq(Trigger(Seq(nPairApp))()),
            viper.silicon.utils.ast.BigAnd(eqs)
          )()
        )(domainName = domainName)
      }

      val tupleOverGetAxiom = {

        val nGetApp = getFuncs map (f =>
          DomainFuncApp(f, Seq(domainVar), typVarMap)()
        )

        DomainAxiom(
          name = s"tuple${arity}_over_getter",
          exp = Forall(
            Seq(domainDecl),
            nGetApp map (g => Trigger(Seq(g))()),
            EqCmp(
              DomainFuncApp(
                tupleFunc,
                nGetApp,
                typVarMap
              )(),
              domainVar
            )()
          )()
        )(domainName = domainName)
      }

      val domain = Domain(
        domainName,
        tupleFunc +: getFuncs,
        Seq(getOverTupleAxiom, tupleOverGetAxiom),
        typeVars
      )()

      domains.update(arity, domain)
      constructors.update(arity, tupleFunc)
      0.until(arity) foreach (ix => getters.update((ix, arity), getFuncs(ix)))

      _generatedDomains ::= domain
    }

    def domain(arity: Int): Domain =
      domains.getOrElse(arity, {addNPairDomain(arity); domains(arity)})
    def tuple(arity: Int): DomainFunc =
      constructors.getOrElse(arity, {addNPairDomain(arity); constructors(arity)})
    def get(index: Int, arity: Int): DomainFunc =
      getters.getOrElse((index, arity), {addNPairDomain(arity); getters((index, arity))})

    def typeVarMap(ts: Vector[Type]) = domain(ts.length).typVars.zip(ts).toMap
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