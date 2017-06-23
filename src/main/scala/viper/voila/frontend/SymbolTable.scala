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

sealed abstract class RegularEntity extends Entity with Product {
  def declaration: PDeclaration
}

object RegularEntity {
  def unapply(entity: RegularEntity): Option[PDeclaration] = Some(entity.declaration)
}

case class ProcedureEntity(declaration: PProcedure) extends RegularEntity
case class PredicateEntity(declaration: PPredicate) extends RegularEntity
case class RegionEntity(declaration: PRegion) extends RegularEntity
case class GuardEntity(declaration: PGuardDecl, region: PRegion) extends RegularEntity

case class ArgumentEntity(declaration: PFormalArgumentDecl) extends RegularEntity
case class LocalVariableEntity(declaration: PLocalVariableDecl) extends RegularEntity
