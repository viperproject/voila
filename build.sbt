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

      scalaVersion := "2.11.11",
      scalacOptions in Compile ++= Seq(
        "-deprecation",
        "-unchecked",
        "-feature",
        // "-Ypatmat-exhaust-depth", "off", // "40"
        "-Xno-patmat-analysis"
        // "-Xstrict-patmat-analysis"
        /*"-Xfatal-warnings"*/),

      /* See also:
       *   https://www.threatstack.com/blog/useful-scalac-options-for-better-scala-development-part-1/
       *   https://tpolecat.github.io/2017/04/25/scalac-flags.html
       */

      libraryDependencies ++= externalDependencies,

      /* Make sure Silicon doesn't overflow the stack */
      javaOptions in run += "-Xss64M",
      javaOptions in Test += "-Xss64M",

      excludeFilter in siliconSrc := "logback.xml", /* Ignore Silicon's Logback configuration */
      unmanagedResourceDirectories in Compile += baseDirectory.value / "conf",

      mainClass in assembly := Some("viper.voila.VoilaRunner"),
      assemblyJarName in assembly := "voila.jar",
      assemblyMergeStrategy in assembly := {
        case LogbackConfigurationFilePattern() => MergeStrategy.discard
        case x => (assemblyMergeStrategy in assembly).value(x)
      },
      test in assembly := {},

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

val LogbackConfigurationFilePattern = """logback.*?\.xml""".r

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
