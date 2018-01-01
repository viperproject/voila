/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.translator

import viper.voila.frontend._
import viper.silver.{ast => vpr}

trait HeapAccessTranslatorComponent { this: PProgramToViperTranslator =>
  def toField(declaredBy: PStruct, id: PIdnNode): vpr.Field = {
    val fieldType = declaredBy.fields.find(_.id.name == id.name).get.typ

    vpr.Field(s"$$${declaredBy.id.name}_$$${id.name}", translate(fieldType))()
  }

  def translate(location: PLocation): vpr.FieldAccess = {
    val recevierType =
      semanticAnalyser.typeOfIdn(location.receiver).asInstanceOf[PRefType]

    val receiverStruct =
      semanticAnalyser.entity(recevierType.id).asInstanceOf[StructEntity].declaration

    vpr.FieldAccess(
      translateUseOf(location.receiver),
      toField(receiverStruct, location.field)
    )()
  }

  def translate(read: PHeapRead): vpr.Stmt = {
    val vprLocalVarType = translate(semanticAnalyser.typeOfIdn(read.lhs))
    val vprLocalVar = vpr.LocalVar(read.lhs.name)(typ = vprLocalVarType).withSource(read.lhs)
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
        case _: PLogicalVariableBinder | _: PIrrelevantValue => vpr.TrueLit()()
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

  def translateAsHeapAccess(id: PIdnNode, declaration: PLogicalVariableBinder): vpr.Exp = {
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
          )()

        case PInterferenceClause(`declaration`, _, regionId) =>
          regionState(semanticAnalyser.usedWithRegionPredicate(regionId))

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

        vpr.Old(vprHeapRead)()

      case (LogicalVariableContext.Procedure, _) =>
        val declAss = semanticAnalyser.enclosingAssertion(declaration)
        val idAss = semanticAnalyser.enclosingAssertion(id)

        if (declAss eq idAss)
          vprHeapRead
        else
          vpr.LocalVar(declaration.id.name)(translate(semanticAnalyser.typeOfIdn(declaration.id)))

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
