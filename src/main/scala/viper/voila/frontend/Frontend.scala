package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.parsing.{Failure, Success}
import org.bitbucket.inkytonik.kiama.util.{Messaging, PositionStore, StringSource}
import org.bitbucket.inkytonik.kiama.util.Messaging.{message, Messages}

class Frontend extends PositionStore with Messaging {
  val syntaxAnalyser = new SyntaxAnalyser(positions)

  def parse(source: String): Either[Messages, PProgram] =
    parse(source, syntaxAnalyser.program)

  protected def parse[T](source: String, parser: syntaxAnalyser.Parser[T]): Either[Messages, T] = {
    positions.reset()

    syntaxAnalyser.parse(parser, StringSource(source)) match {
      case Success(ast, next) =>
        if (next.atEnd)
          Right(ast)
        else
          sys.error(
            s"""Parser error!
               |Parsed: $ast
               |Next: $next
             """.stripMargin)
      case f @ Failure(label, next) =>
        val pos = next.position
        positions.setStart(f, pos)
        positions.setFinish(f, pos)
        val messages = message(f, label)
        Left(messages)
    }
  }
}
