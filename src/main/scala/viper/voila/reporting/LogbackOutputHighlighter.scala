package viper.voila.reporting

import scala.annotation.switch
import ch.qos.logback.classic.Level
import ch.qos.logback.classic.spi.ILoggingEvent
import ch.qos.logback.core.pattern.color.ForegroundCompositeConverterBase
import ch.qos.logback.core.pattern.color.ANSIConstants._

class LogbackOutputHighlighter extends ForegroundCompositeConverterBase[ILoggingEvent] {
  override def getForegroundColorCode(event: ILoggingEvent): String = {
    val level: Level = event.getLevel

    (level.toInt: @switch) match {
      case Level.ERROR_INT => BOLD + RED_FG
      case Level.WARN_INT => YELLOW_FG
//      case Level.INFO_INT => CYAN_FG
      case _ => DEFAULT_FG
    }
  }
}
