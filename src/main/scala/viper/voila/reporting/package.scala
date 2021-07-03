package viper.voila

import scala.language.implicitConversions

package object reporting {
  implicit def liftVerificationErrorToOption(error: VerificationError): Option[VerificationError] = {
    Some(error)
  }
}
