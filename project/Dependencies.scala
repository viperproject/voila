import sbt._

object Dependencies {
  lazy val kiama = "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.1.0"
  lazy val scallop = "org.rogach" %% "scallop" % "2.0.7"
  lazy val logbackClassic = "ch.qos.logback" % "logback-classic" % "1.1.7" // Logging Backend
  lazy val scalaLogging = "com.typesafe.scala-logging" %% "scala-logging" % "3.5.0" // Logging Frontend
  lazy val commonsIO = "commons-io" % "commons-io" % "2.5"

  lazy val silver = "viper" %% "silver" % "0.1-SNAPSHOT"
  lazy val silverSrc = RootProject(new java.io.File("../silver"))

  lazy val silicon = "viper" %% "silicon" % "1.1-SNAPSHOT"
  lazy val siliconSrc = RootProject(new java.io.File("../silicon"))
}
