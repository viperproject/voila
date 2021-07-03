/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.util.{Entity, Environments}

/** A symbol table and its entries */

sealed abstract class VoilaEntity extends Entity with Product

case class MultipleEntity() extends VoilaEntity {
  override val isError = true
}

case class UnknownEntity() extends VoilaEntity {
  override val isError = true
}

class SymbolTable() extends Environments[VoilaEntity]

sealed abstract class RegularEntity extends VoilaEntity with Product {
  def declaration: PDeclaration
}

object RegularEntity {
  def unapply(entity: RegularEntity): Option[PDeclaration] = Some(entity.declaration)
}

case class StructEntity(declaration: PStruct) extends RegularEntity
case class ProcedureEntity(declaration: PProcedure) extends RegularEntity
case class PredicateEntity(declaration: PPredicate) extends RegularEntity
case class RegionEntity(declaration: PRegion) extends RegularEntity
case class GuardEntity(declaration: PGuardDecl, region: PRegion) extends RegularEntity

//sealed trait VariableEntity extends RegularEntity {
//  def declaration: PDeclaration
//}
//
//object VariableEntity {
//  def unapply(entity: VariableEntity): Option[PDeclaration] = Some(entity.declaration)
//}

sealed trait LocalVariableLikeEntity extends VoilaEntity {
  def id: PIdnDef
  def typ: PType
}

case class FormalArgumentEntity(declaration: PFormalArgumentDecl) extends RegularEntity

case class FormalReturnEntity(declaration: PFormalReturnDecl) extends LocalVariableLikeEntity {
  val id: PIdnDef = declaration.id
  val typ: PType = declaration.typ
}

case class LocalVariableEntity(declaration: PLocalVariableDecl) extends LocalVariableLikeEntity  {
  val id: PIdnDef = declaration.id
  val typ: PType = declaration.typ
}

case class LogicalVariableEntity(declaration: PNamedBinder) extends RegularEntity

//// Internal types, not created from user programs by the parser but
//// used to represent some types internally to the semantic analysis.
//
///**
// * A reference type given by the declared class body.
// */
//case class ReferenceType(decl : Class) extends Type
