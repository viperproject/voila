package viper.voila.frontend

import com.typesafe.scalalogging.StrictLogging
import org.bitbucket.inkytonik.kiama.parsing.{Failure, Success}
import org.bitbucket.inkytonik.kiama.util.{Messaging, Position, PositionStore, StringSource}
import org.bitbucket.inkytonik.kiama.util.Messaging.{Messages, message}
import viper.voila.reporting.{ParserError, VoilaError}

class Frontend extends PositionStore with Messaging with StrictLogging {
  val syntaxAnalyser = new SyntaxAnalyser(positions)

  def parse(source: String): Either[Vector[ParserError], PProgram] = {
    parse(source, syntaxAnalyser.phrase(syntaxAnalyser.program)) match {
      case Right(program) => Right(program)
      case Left(messages) => Left(translateToVoilaErrors(messages, ParserError))
    }
  }

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

  def translateToVoilaErrors[E <: VoilaError]
                            (messages: Messages, errorFactory: (String, Position) => E)
                            : Vector[E] = {

    messages.sorted.map(message => {
      val position = positions.getStart(message.value).get
      errorFactory(formatMessage(message), position)
    })
  }
}
