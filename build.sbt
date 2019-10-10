import scala.sys.process.Process
import scala.util.Try

// Import general settings from Silver
lazy val silver = project in file("silver")

// Import general settings from Silicon
lazy val silicon = project in file("silicon")

// Import general settings from Silicon
// lazy val carbon = project in file("carbon")

lazy val voila = (project in file("."))
  .dependsOn(silver % "compile->compile;test->test")
  .dependsOn(silicon % "compile->compile;test->test")
  // .dependsOn(carbon % "compile->compile;test->test")
  .settings(
    /* General settings */
    name := "Voila",
    organization := "viper",
    version := "0.1-SNAPSHOT",
    homepage := Some(url("https://bitbucket.org/viperproject/voila")),
    licenses := Seq("MPL-2.0 License" -> url("https://opensource.org/licenses/MPL-2.0")),

    /* Compilation settings */
    silicon / excludeFilter := "logback.xml", /* Ignore Silicon's Logback configuration */
    // carbon / excludeFilter := "logback.xml", /* Ignore Carbon's Logback configuration */
    Compile / unmanagedResourceDirectories += baseDirectory.value / "conf",
    libraryDependencies +=
      ("org.bitbucket.inkytonik.kiama" %% "kiama" % "2.2.0") // Parsing
        .exclude("com.google.guava", "guava"),
    libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.0", // Logging Frontend
    libraryDependencies += "org.fusesource.jansi" % "jansi" % "1.17.1", // For colouring Logback output

    /* Run settings */
    run / javaOptions += "-Xss128m",

    fork := true,
      /* Serves two purposes:
       *  - http://stackoverflow.com/questions/21464673
       *  - avoid problems on Windows where modifying test files can result in remaining open
       *    file handlers that prevent 'sbt test' from accessing the modifies test file
       */

    /* Test settings */
    Test / javaOptions ++= (run / javaOptions).value,

    /* Assembly settings */
    assembly / assemblyJarName := "voila.jar",
    assembly / mainClass := Some("viper.voila.VoilaRunner"),
    assembly / assemblyMergeStrategy := {
      case LogbackConfigurationFilePattern() => MergeStrategy.discard
      case x => (assemblyMergeStrategy in assembly).value(x)
    },
    assembly / test := {})
  .enablePlugins(BuildInfoPlugin)
  .settings(
    buildInfoKeys := Seq[BuildInfoKey](
      "projectName" -> name.value,
      "projectVersion" -> version.value,
      scalaVersion,
      sbtVersion,
      BuildInfoKey.action("hg") {
        val Seq(revision, branch) =
          Try(
            Process("hg id -ib").!!.trim.split(' ').toSeq
          ).getOrElse(Seq("<revision>", "<branch>"))
        Map("revision" -> revision, "branch" -> branch)
      }
    ),
    buildInfoPackage := "viper.voila")

val LogbackConfigurationFilePattern = """logback.*?\.xml""".r
