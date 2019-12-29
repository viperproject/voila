/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.reporting

import scala.collection.breakOut
import scala.collection.immutable.ListMap

final class VerificationDurationRecord(var parsing: Option[Long] = None,
                                       var typechecking: Option[Long] = None,
                                       var translation: Option[Long] = None,
                                       var consistency: Option[Long] = None,
                                       var verification: Option[Long] = None) {

  val propertyNames: Vector[String] =
    Vector("Parsing", "Typechecking", "Translating", "Consistency checking", "Verifying")

  def asRow: Vector[Option[Long]] =
    Vector(parsing, typechecking, translation, consistency, verification)

  def asValuesRow: Vector[Long] =
    asRow.map(_.getOrElse(0L))

  def asMap: ListMap[String, Option[Long]] =
    propertyNames.zip(asRow)(breakOut)

  def asValuesMap: ListMap[String, Long] =
    propertyNames.zip(asValuesRow)(breakOut)

  override def toString: String = {
    val dataStr =
      asRow
        .map(_.getOrElse('-'))
        .mkString(", ")

    s"${getClass.getSimpleName}($dataStr)"
  }
}
