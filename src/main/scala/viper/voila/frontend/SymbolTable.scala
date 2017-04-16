/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.util.Environments
import org.bitbucket.inkytonik.kiama.util.Entity

/** A symbol table and its entries */

class SymbolTable() extends Environments

sealed abstract class WelldefinedEntity extends Entity with Product {
  def declaration: PDeclaration
}

case class ProcedureEntity(declaration: PProcedure) extends WelldefinedEntity

sealed trait VariableEntity extends WelldefinedEntity {
  def declaration: PTypedDeclaration
}

object VariableEntity {
  def unapply(entity: VariableEntity): Option[PTypedDeclaration] = Some(entity.declaration)
}

case class ArgumentEntity(declaration: PFormalArgumentDecl) extends VariableEntity
case class LocalVariableEntity(declaration: PLocalVariableDecl) extends VariableEntity


//// Internal types, not created from user programs by the parser but
//// used to represent some types internally to the semantic analysis.
//
///**
// * A reference type given by the declared class body.
// */
//case class ReferenceType(decl : Class) extends Type


