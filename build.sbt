import scala.sys.process.{Process, ProcessLogger}
import scala.util.{Failure, Success, Try}

// [2020-10-12 MS]
//   When assembling a fat test JAR (test:assembly), the files under
//   src/test don't end up in tje JAR if the next line is missing.
//   I'm not sure why that is, or why exactly the next line helps.
//   To be investigated.
Project.inConfig(Test)(baseAssemblySettings ++ Seq(Test / assembly / test := {}))

// [2021-07-03 MS] Should be inherited from Silver, but without it, Jenkins appears to
// look for dependencies built against Scala 2.12, which then fails
ThisBuild / scalaVersion := "2.13.4"

// Import general settings from Silver
lazy val silver = project in file("silver")

// Import general settings from Silicon
lazy val silicon = project in file("silicon")

//// Import general settings from Carbon
//lazy val carbon = project in file("carbon") [CARBON]

lazy val voila = (project in file("."))
  .dependsOn(silver % "compile->compile;test->test")
  .dependsOn(silicon % "compile->compile;test->test")
//  .dependsOn(carbon % "compile->compile;test->test") [CARBON]
  .settings(
    /* General settings */
    name := "Voila",
    organization := "viper",
    version := "0.1-SNAPSHOT",
    homepage := Some(url("https://github.com/viperproject/voila")),
    licenses := Seq("MPL-2.0 License" -> url("https://opensource.org/licenses/MPL-2.0")),

    /* Compilation settings */
    silicon / excludeFilter := "logback.xml", /* Ignore Silicon's Logback configuration */
//    carbon / excludeFilter := "logback.xml", /* Ignore Carbon's Logback configuration */ [CARBON]
    Compile / unmanagedResourceDirectories += baseDirectory.value / "conf",
    libraryDependencies += "org.scala-lang.modules" %% "scala-collection-contrib" % "0.2.2", // MultiDict collection
    libraryDependencies +=
      ("org.bitbucket.inkytonik.kiama" %% "kiama" % "2.4.0") // Parsing
        .exclude("com.google.guava", "guava"),
    libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.2", // Logging Frontend
    libraryDependencies += "org.fusesource.jansi" % "jansi" % "2.1.0", // For colouring Logback output

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
      case LogbackConfigurationFilePattern() =>
        MergeStrategy.discard
      case PathList("viper", "silicon", ps @ _*)
              if ps.nonEmpty && ps.last.startsWith("BuildInfo") && ps.last.endsWith(".class") =>
        /* On Jenkins, it seems that two copies of class viper.silicon.BuildInfo get assembly-ed:
         * One is contained in Silicon's fat JAR (copied into Voila's workspace as lib/silicon.jar),
         * the other one is locally generated (silicon/target/scala-XX/classes). The latter is
         * probably locally generated because the corresponding Scala source file is also locally
         * generated (silicon/target/scala-XX/src_managed) by the sbt-buildinfo plugin, probably
         * upon loading Silicon's build.sbt, which is also copied into Voila's workspace.
         * 
         * To work around the problem, we simply keep the first copy that is encountered. Note that
         * this is most likely not what we actually want. E.g. it could contain an incorrect (most
         * likely newer) build timestamp, or even Voila's Git revision instead of Silicon's.
         */
        MergeStrategy.first
      case x =>
        (assemblyMergeStrategy in assembly).value(x)
    },
    assembly / test := {})
  .enablePlugins(BuildInfoPlugin)
  .settings(
    buildInfoKeys := Seq[BuildInfoKey](
      "projectName" -> name.value,
      "projectVersion" -> version.value,
      scalaVersion,
      sbtVersion,
      "gitRevision" -> gitInfo.value._1,
      "gitBranch" -> gitInfo.value._2
    ),
    buildInfoPackage := "viper.voila")

/// Pair of revision and branch information from Git. Empty strings if an error occurred.
lazy val gitInfo: Def.Initialize[(String, String)] = Def.setting {
  val gitCommand = "git status --porcelain=v2 --branch"

  Try({
    val outputBuffer = new StringBuffer()

    // Execute Git, record stdout and stderr in outputBuffer, and return the exit code
    val exitCode =
      Process(gitCommand, baseDirectory.value).!(ProcessLogger(outputBuffer append _ append '\n'))

    if (exitCode != 0)
      sys.error(s"'$gitCommand' didn't execute successfully")

    val output = outputBuffer.toString
    val lines = output.split('\n').map(_.trim)

    // Expected format is "# branch.oid HASH", use first 8 digits
    var revision = lines.find(_.startsWith("# branch.oid")).get.split(' ')(2).take(8)

    // Expected format is "# branch.head NAME"
    val branch = lines.find(_.startsWith("# branch.head")).get.split(' ')(2)

    if (!lines.forall(_.startsWith("# ")))
      revision = s"$revision+"

    Seq(revision, branch)
  }) match {
    case Failure(throwable) =>
      sLog.value.warn(s"Couldn't execute '${throwable.getMessage}', or couldn't parse obtained output")
      ("", "")
    case Success(Seq(revision, branch)) =>
      (revision, branch)
  }
}

val LogbackConfigurationFilePattern = """logback.*?\.xml""".r
