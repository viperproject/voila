package viper.voila.frontend

import org.bitbucket.inkytonik.kiama.parsing.{Failure, Success}
import org.bitbucket.inkytonik.kiama.util.{Messaging, PositionStore, StringSource}
import org.bitbucket.inkytonik.kiama.util.Messaging.{message, Messages}

/**
  * Created by malte on 14-Apr-17.
  */
class Frontend extends PositionStore with Messaging {
  val syntaxAnalyser = new SyntaxAnalyser(positions)

  def parse(source: String): Either[Messages, PProgram] =
    parse(source, syntaxAnalyser.program)

  protected def parse[T](source: String, parser: syntaxAnalyser.Parser[T]): Either[Messages, T] = {
    positions.reset()

    syntaxAnalyser.parse(parser, StringSource(source)) match {
      case Success(ast, _) =>
        Right(ast)
      case f @ Failure(label, next) =>
        val pos = next.position
        positions.setStart(f, pos)
        positions.setFinish(f, pos)
        val messages = message(f, label)
        Left(messages)
    }
  }
}
