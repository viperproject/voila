/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.voila.frontend._
import viper.silver.{ast => vpr}

trait HeapAccessTranslatorComponent { this: PProgramToViperTranslator =>
  private def heapLocationAsField(typ: PType): vpr.Field =
    vpr.Field(s"$$h_$typ", translateNonVoid(typ))()

  private def referencedType(id: PIdnNode): PType =
    semanticAnalyser.referencedType(semanticAnalyser.typeOfIdn(id))

  def heapLocations(tree: VoilaTree): Vector[vpr.Field] = {
    tree.nodes.collect {
      case access: PHeapAccess => heapLocationAsField(referencedType(access.location))
      case pointsTo: PPointsTo => heapLocationAsField(referencedType(pointsTo.id))
    }.distinct
  }

  def translate(read: PHeapRead): vpr.Stmt = {
    val voilaType = referencedType(read.location)
    val viperType = translateNonVoid(voilaType)

    val rcvr = vpr.LocalVar(read.location.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)
    val lv = vpr.LocalVar(read.lhs.name)(typ = viperType)

    vpr.LocalVarAssign(lv, vpr.FieldAccess(rcvr, fld)())()
  }

  def translate(write: PHeapWrite): vpr.Stmt = {
    val voilaType = referencedType(write.location)

    val rcvr = vpr.LocalVar(write.location.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)

    vpr.FieldAssign(vpr.FieldAccess(rcvr, fld)(), translate(write.rhs))()
  }

  def translate(pointsTo: PPointsTo): vpr.Exp = {
    val voilaType = referencedType(pointsTo.id)

    val rcvr = vpr.LocalVar(pointsTo.id.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)
    val deref = vpr.FieldAccess(rcvr, fld)()

    val fldvalcnstr = pointsTo.value match {
      case _: PLogicalVariableBinder => vpr.TrueLit()()
      case exp => vpr.EqCmp(deref, translate(exp))()
    }

    vpr.And(
      vpr.FieldAccessPredicate(deref, vpr.FullPerm()())(),
      fldvalcnstr
    )()
  }

  def translateUseOf(id: PIdnNode, declaration: PLogicalVariableBinder): vpr.Exp = {
    val generalBindingContext = semanticAnalyser.generalBindingContext(declaration)
    val generalUsageContext = semanticAnalyser.generalUsageContext(id)

    val vprHeapRead: vpr.Exp =
      semanticAnalyser.boundBy(declaration) match {
        case PPointsTo(location, _) =>
          val voilaType = semanticAnalyser.typeOfIdn(declaration.id)
          val vprReceiver = vpr.LocalVar(location.name)(typ = vpr.Ref)
          val vprField = heapLocationAsField(voilaType)

          vpr.FieldAccess(vprReceiver, vprField)()

        case predicateExp: PPredicateExp =>
          regionState(predicateExp)

        case PInterferenceClause(`declaration`, set, regionId) =>
          regionState(semanticAnalyser.usedWithRegionPredicate(regionId))

        case other =>
          sys.error(s"Unexpectedly found $other")
      }

    (generalBindingContext, generalUsageContext) match {
      case (LogicalVariableContext.Precondition, LogicalVariableContext.Precondition) |
           (LogicalVariableContext.Interference, LogicalVariableContext.Interference) |
           (LogicalVariableContext.Interference, LogicalVariableContext.Precondition) |
           (LogicalVariableContext.Postcondition, LogicalVariableContext.Postcondition) |
           (LogicalVariableContext.Region, LogicalVariableContext.Region) |
           (LogicalVariableContext.Predicate, LogicalVariableContext.Predicate) =>

        vprHeapRead

      case (LogicalVariableContext.Precondition, _) |
           (LogicalVariableContext.Interference, _) =>

        vpr.Old(vprHeapRead)()

      case other =>
        sys.error(s"Unexpectedly found $other")
    }
  }
}
