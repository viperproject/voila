import Dependencies._

lazy val voila = {
  var project = Project(
    id = "voila",
    base = file("."),
    settings = Seq(
      organization := "viper",
      name := "Voila",
      version := "0.1.0-SNAPSHOT",
      homepage := Some(url("https://bitbucket.org/mschwerhoff/voila")),
      licenses := Seq("MPL-2.0 License" -> url("https://opensource.org/licenses/MPL-2.0")),

      scalaVersion := "2.11.8",
      scalacOptions in Compile ++= Seq(
        "-deprecation",
        "-unchecked",
        "-feature"
        /*"-Xfatal-warnings"*/),

      libraryDependencies ++= externalDependencies,

      fork := true
        /* Serves two purposes:
         *  - http://stackoverflow.com/questions/21464673
         *  - avoid problems on Windows where modifying test files can result in remaining open
         *    file handlers that prevent 'sbt test' from accessing the modifies test file
         */
    ))

  for (dep <- internalDependencies) {
    project = project.dependsOn(dep)
  }

  project
}

lazy val internalDependencies =
  if (isBuildServer)
    Nil
  else
    Seq(silverSrc % "compile->compile;test->test",
        siliconSrc % "compile->compile;test->test")

lazy val externalDependencies = (
     Seq(kiama, scallop, logbackClassic, scalaLogging, commonsIO)
  ++ (if (isBuildServer)
       Seq(silver % "compile->compile;test->test",
           silicon % "compile->compile;test->test")
      else
       Nil))

addCommandAlias("to", "test-only")
addCommandAlias("tn", "test-only -- -n")

lazy val isBuildServer =
  sys.env.contains("BUILD_TAG") /* Should only be defined on the build server */