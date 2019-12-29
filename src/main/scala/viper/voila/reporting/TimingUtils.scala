/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila.reporting

/** Assuming that [[viper.silver.utility.TimingUtils]] is thread-safe, then this object is, too.
  */
object TimingUtils extends viper.silver.utility.TimingUtils {
  def startTimer(): Timer = new Timer().start()
}

/** Note: Timer objects are not thread-safe. */
class Timer() {
  var startTimeMillis: Long = _
  var endTimeMillis: Long = _
  var durationMillis: Long = _

  reset()

  def start(): this.type = {
    reset()

    startTimeMillis = System.currentTimeMillis()

    this
  }

  def stop(): this.type = {
    endTimeMillis = System.currentTimeMillis()
    durationMillis = endTimeMillis - startTimeMillis

    this
  }

  def reset(): this.type = {
    startTimeMillis = -1
    endTimeMillis = -1
    durationMillis = -1

    this
  }

  def pretty(): String = TimingUtils.formatTime(durationMillis)
}
