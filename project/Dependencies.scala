import sbt._

object Dependencies {
  lazy val scalaTest = "org.scalatest" %% "scalatest" % "3.0.1"
  lazy val kiama = "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.0.0"
  lazy val scallop = "org.rogach" %% "scallop" % "2.0.7"
//  lazy val logbackClassic = "ch.qos.logback" % "logback-classic" % "1.1.7"
//  lazy val slf4s = "org.slf4s" %% "slf4s-api" % "1.7.12"
  lazy val slf4j = "org.slf4j" % "slf4j-log4j12" % "1.7.22"
  lazy val scalaLogging = "com.typesafe.scala-logging" %% "scala-logging" % "3.5.0"
  lazy val commonsIO = "commons-io" % "commons-io" % "2.5"

  lazy val silverSrc = RootProject(new java.io.File("../transformations/silver"))
}
