/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.voila.frontend._
import viper.silver.{ast => vpr}

trait HeapAccessTranslatorComponent { this: PProgramToViperTranslator =>
  def toField(declaredBy: PMemberWithFields, id: PIdnNode): vpr.Field = {
    val fieldType = declaredBy.fields.find(_.id.name == id.name).get.typ

    vpr.Field(
      s"$$${declaredBy.id.name}_$$${id.name}",
      translate(fieldType)
    )().withSource(id)
  }

  def translate(location: PLocation): vpr.FieldAccess = {
    val receiverMember: PMemberWithFields =
      semanticAnalyser.typeOfIdn(location.receiver.id) match {
        case referenceType: PRefType =>
          semanticAnalyser.entity(referenceType.id).asInstanceOf[StructEntity].declaration

        case _: PRegionIdType =>
          semanticAnalyser.usedWithRegion(location.receiver.id)

        case other =>
          sys.error(s"Unexpectedly found $other")
      }

    vpr.FieldAccess(
      translateUseOf(location.receiver.id),
      toField(receiverMember, location.field)
    )().withSource(location)
  }

  def translate(read: PHeapRead): vpr.Stmt = {
    val vprLocalVarType = translate(semanticAnalyser.typeOfIdn(read.lhs))
    val vprLocalVar = vpr.LocalVar(read.lhs.name, vprLocalVarType)().withSource(read.lhs)
    val vprFieldAccess = translate(read.location)

    vpr.LocalVarAssign(
      vprLocalVar,
      vprFieldAccess
    )().withSource(read)
  }

  def translate(write: PHeapWrite): vpr.Stmt = {
    vpr.FieldAssign(
      translate(write.location),
      translate(write.rhs)
    )().withSource(write)
  }

  def translate(pointsTo: PPointsTo): vpr.Exp = {
    val vprFieldAccess = translate(pointsTo.location)

    val vprFieldValueConstraint =
      pointsTo.value match {
        case _: PLogicalVariableBinder => vpr.TrueLit()()
        case exp => vpr.EqCmp(vprFieldAccess, translate(exp))()
      }

    vpr.And(
      vpr.FieldAccessPredicate(
        vprFieldAccess,
        vpr.FullPerm()()
      )().withSource(pointsTo.location),
      vprFieldValueConstraint
    )()
  }

  def translateAsHeapAccess(id: PIdnNode, declaration: PNamedBinder): vpr.Exp = {
    val generalBindingContext = semanticAnalyser.generalBindingContext(declaration)
    val generalUsageContext = semanticAnalyser.generalUsageContext(id)

    val vprHeapRead: vpr.Exp =
      semanticAnalyser.boundBy(declaration) match {
        case PPointsTo(location, _) =>
          translate(location)

        case predicateExp: PPredicateExp =>
          val (region, inArgs, outArgs) = getRegionPredicateDetails(predicateExp)
          val idx = outArgs.indexOf(declaration)

          assert(idx != -1)

          vpr.FuncApp(
            regionOutArgumentFunction(region, idx),
            inArgs map translate
          )().withSource(id)

        case inter @ PInterferenceClause(`declaration`, _, _) =>
          val regionId = semanticAnalyser.interferenceOnRegionId(inter)
          regionState(semanticAnalyser.usedWithRegionPredicate(regionId)).withSource(id)

        case other =>
          sys.error(s"Unexpectedly found $other")
      }

    (generalBindingContext, generalUsageContext) match {
      case (LogicalVariableContext.Precondition, LogicalVariableContext.Precondition) |
           (LogicalVariableContext.Interference, LogicalVariableContext.Interference) |
           (LogicalVariableContext.Interference, LogicalVariableContext.Precondition) |
           (LogicalVariableContext.Postcondition, LogicalVariableContext.Postcondition) |
           (LogicalVariableContext.Invariant, LogicalVariableContext.Invariant) |
           (LogicalVariableContext.Region, LogicalVariableContext.Region) |
           (LogicalVariableContext.Predicate, LogicalVariableContext.Predicate) =>

        vprHeapRead

      case (LogicalVariableContext.Precondition, _) |
           (LogicalVariableContext.Interference, _) =>

        vpr.Old(vprHeapRead)().withSource(id)

      case (LogicalVariableContext.Procedure, _) =>
        val declAss = semanticAnalyser.enclosingAssertion(declaration)
        val idAss = semanticAnalyser.enclosingAssertion(id)

        if (declAss eq idAss) {
          vprHeapRead
        } else {
          val vprType = translate(semanticAnalyser.typeOfIdn(declaration.id))

          vpr.LocalVar(declaration.id.name, vprType)().withSource(id)
        }

      case _ =>
        sys.error(
          s"""Unexpected situation:
             |  id = $id
             |  declaration = $declaration
             |  generalBindingContext = $generalBindingContext
             |  generalUsageContext = $generalUsageContext
           """.stripMargin)
    }
  }
}
