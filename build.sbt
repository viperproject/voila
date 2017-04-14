import Dependencies._

lazy val root = (project in file(".")).
  settings(
    organization := "viper",
    name := "Voila",
    version := "0.1.0-SNAPSHOT",

    homepage := Some(url("https://github.com/jvican/stoml")),
    licenses := Seq("MPL-2.0 License" -> url("https://opensource.org/licenses/MPL-2.0")),

    scalaVersion := "2.12.1",

    libraryDependencies += scalaTest % Test,
    libraryDependencies += kiama
  )

addCommandAlias("to", "test-only")
addCommandAlias("tn", "test-only -- -n")