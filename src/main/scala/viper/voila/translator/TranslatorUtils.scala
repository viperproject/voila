/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.silver.ast._

import scala.collection.mutable
import viper.silver.{ast => vpr}
import viper.voila.frontend.PMember

object TranslatorUtils {

  trait BasicFootprintManager[R] {

    val name: String = getClass.getSimpleName

    def nameObject(obj: R): String

    def footprintName(objName: String): String = s"${objName}_${name}_fp"

    /* Maps regions to corresponding footprints */
    protected val collectedFootprints = mutable.Map.empty[String, vpr.Predicate]

    def objectArgSelection(obj: R): Vector[vpr.LocalVarDecl]
    def selectObjectArgs(obj: R, args: Vector[vpr.Exp]): Vector[vpr.Exp]

    def collectFooprint(obj: R): vpr.Predicate = {
      val footprintPredicate =
        vpr.Predicate(
          name = footprintName(nameObject(obj)),
          formalArgs = objectArgSelection(obj),
          body = None
        )()

      collectedFootprints += nameObject(obj) -> footprintPredicate

      footprintPredicate
    }

    def footprintAccess(obj: R, args: Vector[vpr.Exp])
    : vpr.PredicateAccessPredicate =
      vpr.PredicateAccessPredicate(
        vpr.PredicateAccess(
          predicateName = footprintName(nameObject(obj)),
          args = selectObjectArgs(obj, args)
        )(),
        vpr.FullPerm()()
      )()
  }

  trait BasicFootprintFunctionManager[R,F] extends BasicFootprintManager[R] {

    def nameFeature(feature: F): String

    def functionName(objName: String, featureName: String) =
      s"${objName}_${name}_${featureName}_fpf"

    /* Maps pairs of R and F to corresponding footprint dependent functions */
    protected val collectedFunctions = mutable.Map.empty[(String, String), vpr.Function]

    def featureArgSelection(obj: R, feature: F): Vector[vpr.LocalVarDecl]
    def selectFeatureArgs(obj: R, feature: F, args: Vector[vpr.Exp]): Vector[vpr.Exp]

    def collectFeatures(obj: R): Vector[F]
    def functionTyp(obj: R, feature: F): vpr.Type

    def collectAllFunctions(obj: R): Vector[vpr.Function] =
      collectFeatures(obj) map (f => collectFunction(obj,f))

    def collectFunction(obj: R, feature: F): vpr.Function = {
      val decls = featureArgSelection(obj, feature)
      val vars = decls map (_.localVar)

      val function =
        vpr.Function(
          name = functionName(nameObject(obj), nameFeature(feature)),
          formalArgs = decls,
          typ = functionTyp(obj,feature),
          pres = Vector(footprintAccess(obj, vars)),
          posts = Vector.empty,
          decs = None,
          body = None
        )()

      collectedFunctions += (nameObject(obj), nameFeature(feature)) -> function

      function
    }

    def functionApplication(obj: R, feature: F, args: Vector[vpr.Exp]): vpr.FuncApp =
      vpr.FuncApp(
        func = collectedFunctions(nameObject(obj), nameFeature(feature)),
        args = selectFeatureArgs(obj, feature, args)
      )()
  }

  trait BasicFootprintFunctionManagerNoFeature[R] extends BasicFootprintFunctionManager[R, Null] {
    override def nameFeature(feature: Null): String = ""

    def functionArgSelection(obj: R): Vector[vpr.LocalVarDecl]
    def selectFunctionArgs(obj: R, args: Vector[vpr.Exp]): Vector[vpr.Exp]
    def functionTyp(obj: R): vpr.Type

    override def featureArgSelection(obj: R, feature: Null): Vector[LocalVarDecl] = functionArgSelection(obj)

    override def selectFeatureArgs(obj: R, feature: Null, args: Vector[Exp]): Vector[Exp] = selectFunctionArgs(obj, args)

    override def functionTyp(obj: R, feature: Null): Type = functionTyp(obj)

    def collectFeatures(obj: R): Vector[Null] = Vector(null)

    def functionApplication(obj: R, args: Vector[Exp]): FuncApp = functionApplication(obj, null, args)
  }

  trait MemberBasedFootprintNames[R <: PMember] extends BasicFootprintManager[R] {
    override def nameObject(obj: R): String = obj.id.name
  }

  trait EmptyFootprintSelection[R] extends BasicFootprintManager[R] {
    override def objectArgSelection(obj: R): Vector[LocalVarDecl] = Vector.empty
    override def selectObjectArgs(obj: R, args: Vector[Exp]): Vector[Exp] = Vector.empty

    def footprintAccess(obj: R): PredicateAccessPredicate = footprintAccess(obj, Vector.empty)
  }

}
