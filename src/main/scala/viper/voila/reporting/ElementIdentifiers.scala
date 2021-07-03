/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.reporting

import org.bitbucket.inkytonik.kiama.util.Entity
import viper.voila.frontend._
import viper.voila.reporting.ElementIdentifier.{Article, Mode}

object ElementIdentifier {
  sealed trait Article

  object Article {
    case object None extends Article
    case object Definite extends Article
    case object Indefinite extends Article
  }

  sealed trait Mode

  object Mode {
    case object Auto extends Mode
    case object Vowel extends Mode
    case object Consonant extends Mode
  }

  def withArticle(element: String, article: Article, mode: Mode): String = {
    val articleString =
      article match {
        case Article.None => ""
        case Article.Definite => "the"
        case Article.Indefinite =>
          if (mode == Mode.Vowel ||
              mode == Mode.Auto && Set('a', 'e', 'o', 'u').contains(element(0))) {

            "an"
          } else {
            "a"
          }
      }

    s"$articleString $element"
  }
}

object EntityIdentifier {
  private def identify(entity: Entity): (String, Option[String]) = {
    entity match {
      case _ if entity.isError => ("error entity", None)
      case StructEntity(declaration) => ("struct", Some(declaration.id.name))
      case ProcedureEntity(declaration) => ("procedure", Some(declaration.id.name))
      case PredicateEntity(declaration) => ("predicate", Some(declaration.id.name))
      case RegionEntity(declaration) => ("region", Some(declaration.id.name))
      case GuardEntity(declaration, _) => ("guard", Some(declaration.id.name))
      case FormalArgumentEntity(declaration) => ("formal argument", Some(declaration.id.name))
      case LogicalVariableEntity(declaration) => ("logical variable", Some(declaration.id.name))
    }
  }

  def kind(entity: Entity, article: Article = Article.None): String = {
    val entityKind = identify(entity)._1

    ElementIdentifier.withArticle(entityKind, article, Mode.Auto)
  }

  def name(entity: Entity): Option[String] = identify(entity)._2

  def fullyQualified(entity: Entity): String = {
    val (entityKind, optEntityName) = identify(entity)

    s"$entityKind${optEntityName.fold("")(name => s" $name")}"
  }
}

object PIdnNodeIdentifier {
  def fullyQualified(idn: PIdnNode, entity: Entity, article: Article = Article.None): String = {
    val fullyQualifiedName =
      entity match {
        case _: UnknownEntity => s"unknown identifier ${idn.name}"
        case _: MultipleEntity => s"multiply declared identifier ${idn.name}"
        case _ => s"${EntityIdentifier.kind(entity)} ${idn.name}"
      }

    ElementIdentifier.withArticle(fullyQualifiedName, article, Mode.Auto)
  }
}
