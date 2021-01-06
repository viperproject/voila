package viper.voila.frontend

import java.nio.file.Path
import com.typesafe.scalalogging.StrictLogging
import org.bitbucket.inkytonik.kiama.parsing.{NoSuccess, Success}
import org.bitbucket.inkytonik.kiama.util.Messaging.{Messages, message}
import org.bitbucket.inkytonik.kiama.util._
import viper.voila.reporting.{ParserError, VoilaError}

class Frontend extends StrictLogging {
  val positions = new Positions
  val messaging = new Messaging(positions)

  val syntaxAnalyser = new SyntaxAnalyser(positions)

  def parse(file: Path): Either[Vector[ParserError], PProgram] = {
    parse(FileSource(file.toFile.getPath))
  }

  def parse(content: String): Either[Vector[ParserError], PProgram] = {
    parse(StringSource(content))
  }

  protected def parse[T](source: Source): Either[Vector[ParserError], PProgram] = {
    parse(source, syntaxAnalyser.phrase(syntaxAnalyser.program)) match {
      case Right(program) => Right(program)
      case Left(messages) => Left(translateToVoilaErrors(messages, ParserError))
    }
  }

  protected def parse[T](source: Source, parser: syntaxAnalyser.Parser[T])
                        : Either[Messages, T] = {

    positions.reset()

    syntaxAnalyser.parse(parser, source) match {
      case Success(ast, _) =>
        Right(ast)
      case ns @ NoSuccess(label, next) =>
        val pos = next.position
        positions.setStart(ns, pos)
        positions.setFinish(ns, pos)
        val messages = message(ns, label)
        Left(messages)
    }
  }

  def translateToVoilaErrors[E <: VoilaError]
                            (messages: Messages, errorFactory: (String, Position) => E)
                            : Vector[E] = {

    messages.sorted(messaging.messageOrdering).map(message => {
      val position = positions.getStart(message.value).get
      errorFactory(messaging.formatMessage(message), position)
    })
  }
}