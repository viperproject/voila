import Dependencies._

lazy val root =
  (project in file("."))
    .settings(
      organization := "viper",
      name := "Voila",
      version := "0.1.0-SNAPSHOT",

      homepage := Some(url("https://github.com/jvican/stoml")),
      licenses := Seq("MPL-2.0 License" -> url("https://opensource.org/licenses/MPL-2.0")),

      scalaVersion := "2.11.8",

      libraryDependencies += kiama,
      libraryDependencies += scallop,
      libraryDependencies += logbackClassic,
      libraryDependencies += scalaLogging,
      libraryDependencies += commonsIO,

      fork := true
        /* Serves two purposes:
         *  - http://stackoverflow.com/questions/21464673
         *  - avoid problems on Windows where modifying test files can result in remaining open
         *    file handlers that prevent 'sbt test' from accessing the modifies test file
         */
      /* Disable if tests fail unexpectedly */
    ).dependsOn(silverSrc, siliconSrc)

addCommandAlias("to", "test-only")
addCommandAlias("tn", "test-only -- -n")

