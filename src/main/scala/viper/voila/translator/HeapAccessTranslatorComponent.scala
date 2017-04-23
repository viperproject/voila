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
    val fldacc = vpr.FieldAccess(rcvr, fld)()

    val fldvalcnstr = pointsTo.value match {
      case Left(_: PLogicalVariableDecl) => vpr.TrueLit()()
      case Right(exp) => vpr.EqCmp(fldacc, translate(exp))()
    }

    vpr.And(
      vpr.FieldAccessPredicate(fldacc, vpr.FullPerm()())(),
      fldvalcnstr
    )()
  }

  def translateUseOf(declaration: PLogicalVariableDecl): vpr.FieldAccess = {
    val boundTo = semanticAnalyser.boundTo(declaration)
    val voilaType = semanticAnalyser.typeOfIdn(declaration.id)

    val rcvr = vpr.LocalVar(boundTo.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)

    vpr.FieldAccess(rcvr, fld)()
  }
}