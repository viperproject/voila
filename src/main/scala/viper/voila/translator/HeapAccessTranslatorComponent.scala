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
      case access: PAccess  => heapLocationAsField(referencedType(access.location))
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

  def translate(access: PAccess): vpr.Exp = {
    val deref = translateHeapDeref(access.location)

    vpr.FieldAccessPredicate(deref, vpr.FullPerm()())()
  }

  def translateHeapDeref(location: PIdnUse): vpr.FieldAccess = {
    val voilaType = referencedType(location)

    val rcvr = vpr.LocalVar(location.name)(typ = vpr.Ref)
    val fld = heapLocationAsField(voilaType)

    vpr.FieldAccess(rcvr, fld)()
  }
}
