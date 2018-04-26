# voila README

Basic Visual Studio Code support for Voila.

## Syntax highlighting

### Install extension

- Locate VSCode's extension directory:
  - Windows: `%USERPROFILE%\.vscode\extensions`
  - Mac: `$HOME/.vscode/extensions`
  - Linux: `$HOME/.vscode/extensions`
- Create a new extension directory, e.g. `%USERPROFILE%\.vscode\extensions\voila`
- Copy the *content* of the `extension` directory into the newly 
  created extension directory
- Restart VSCode and open a `.vl` file, it should be highlighted

### Fine-tune highlighting

- Switch to VSCode theme `Visual Studio Dark` (potentially called
  `Dark (Visual Studio)`)
- Open your user settings (File -> Preferences -> Settings)
- Copy the following configuration block into your user settings:
 
      "editor.tokenColorCustomizations": {
        "[Visual Studio Dark]": {
          "textMateRules": [
            {
              "scope": [
                "keyword.control.voila",
                "keyword.clauses.voila",
                "keyword.control.ghost.voila",
                "keyword.control.rules.voila",
                "constant.language.voila",
                "constant.numeric.voila",
                "keyword.control.guard-modifiers.voila"
              ],
              "settings": {
                "foreground": "#DCE0AD"
              }
            },
            {
              "scope": [
                "storage.type.buildin.voila",
                "storage.type.struct.voila"
              ],
              "settings": {
                "foreground": "#9cdcfe"
              }
            },
            {
              "scope": "keyword.control.atomicity-modifiers.voila",
              "settings": {
                "foreground": "#B56100"
              }
            },
            {
              "scope": "keyword.control.toplevel.voila",
              "settings": {
                "foreground": "#ffe23e"
              }
            },
          ]
        }
      }

  The effect should be visible immediately.

## Executing Voila programs

There are at least three different ways to nicely run Voila from inside VSCode:

1. Using the Code Runner VSCode plugin
2. Using VSCode's `tasks.json` configuration
3. Windows: using AutoHotkey and MSYS2

On Windows, it is (or at least was, at the time of writing) surprisingly
tricky to make use of Voila's possibility to colour its output (e.g. highlight
errors messages in red), which can be achieved by passing an appropriate
Logback configuration file (e.g. `conf/logback-color.xml`) to the JVM
that runs Voila.
- VSCode's *output channels* (used by the Code Runner plugin) don't appear to 
  render ANSI colour escape codes
- `cmd.exe` displays ANSI colours (if `conf/logback-jansi-color.xml` is used),
  *but not* if Voila is run through Nailgun 
  (my guess is that the `jansi` library that enables ANSI colours for Java 
  on Windows doesn't recognise Nailgun's "output sink" (see the Nailgun section 
  further down) as ready for ANSI colours and thus suppresses/strips out the 
  escape codes)
- Any Bash that is executed as a VSCode integrated terminal appears to loose
  (at least on Windows) the capability of correctly rendering ANSI colours
  even if the Bash works fine (if `conf/logback-color.xml` is used) outside of
  VSCode.

### 1. Using the Code Runner VSCode plugin

#### Installation

##### Default installation and configuration

- Install the 
  [Code Runner](https://marketplace.visualstudio.com/items?itemName=formulahendry.code-runner) 
  extension
- Restart VSCode and open a Voila (`.vl`) file: a triangular run ("play") button 
  should be shown in the top right window corner (on the tab bar)
- Copy the following configuration block into your user settings:

      "code-runner.executorMapByFileExtension": {
        ".vl": "path/to/voila -i $fullFileName"
      },
      "code-runner.clearPreviousOutput": true,
      "code-runner.showExecutionMessage": false,
      "code-runner.ignoreSelection": true,
      "code-runner.enableAppInsights": false,
      "code-runner.runInTerminal": false

  Adjust the path to Voila in the setting `code-runner.executorMapByFileExtension` 
  as needed
- Select the open Voila file and press the run button (or use the keyboard 
  shortcut `Ctrl+Alt+N`. The output panel should open and Voila should be 
  executed on the provided file.

##### Alternative configurations

- The previous configuration yields a so-called *output channel* (VSCode 
  terminology) for Voila's output. It is apparently somehow possible to apply a
  grammar definition to such output channels in order to highlight the output.
  I don't know how to do that, though.
  An alternative is to run Voila in VSCode's built-in terminal. To do so, add 
  the following line to your user settings:

      "code-runner.runInTerminal": true

  What VSCode uses as its built-in terminal can be configured as well. Here are
  four examples for Windows (which I found online):

      /* 1. Use Cmd instead of the default PowerShell */
      "terminal.integrated.shell.windows": "C:\\Windows\\System32\\cmd.exe"

      /* 2a. Use the Bash that comes with Git for Windows */
      "terminal.integrated.shell.windows": "C:\\Program Files\\Git\\bin\\bash.exe"

      /* 2b. Use the pimped Cmd that comes with Git for Windows */
      "terminal.integrated.shell.windows": "C:\\Program Files\\Git\\git-cmd.exe",
      "terminal.integrated.shellArgs.windows": [
        "--command=usr/bin/bash.exe",
        "-l",
        "-i"
      ],

      /* 3. Use the Bash that comes with MSYS2 */
      "terminal.integrated.shell.windows": "C:\\msys64\\msys2_shell.cmd",
      "terminal.integrated.shellArgs.windows": ["-defterm", "-mingw64", "-no-start"]

      /* 4. Use the Bash that comes with Windows 10's Windows Subsystem for Linux */
      "terminal.integrated.shell.windows": "C:\\Windows\\sysnative\\bash.exe"

### 2. Using VSCode's `tasks.json` configuration

- This method only works if you open a project directory 
  (`File` -> `Open Folder...`) from VSCode that contains the Voila files to 
  verify
- If `demo` is the directory that contains the Voila files to verify, then
  create the subdirectory `demo/.vscode`
- Create a file `demo/.vscode/tasks.json` with the following content 
  (the commented lines stem from several experiments and might become useful
  in the future; moreover, the configuration assumes that Voila is run via 
  Nailgun on Windows):

      {
        // See https://go.microsoft.com/fwlink/?LinkId=733558
        // for the documentation about the tasks.json format
        "version": "2.0.0",
        "tasks": [
          {
            "label": "Run Voila",
            "type": "shell",
            "windows": {
              "command": "D:/Develop/Viper/voila/misc/nailgun/voila.bat"

            /* See https://github.com/Microsoft/vscode/issues/36216#issuecomment-336408928 */
            //   "options": {
            //     "shell": {
            //       "executable": "cmd.exe",
            //       "args": [
            //         "/d", "/c"
            //       ]
            //     }
            //   },
            },
            "args": [
              "ng=true",
              "-i",
              "${file}"
            ],
            "group": {
              "kind": "build",
              "isDefault": true
            },
            "presentation": {
              "reveal": "always",
              "panel": "new",
              "echo": false
            }
            /* See https://code.visualstudio.com/Docs/editor/tasks#_defining-a-problem-matcher */
            // "problemMatcher": {
            //   "owner": "vl",
            //   // "fileLocation": ["relative", "${workspaceFolder}"],
            //   "fileLocation": "absolute",
            //   "pattern": {
            //     "regexp": "^\\s*Assert might fail\\.(.*?\\.)\\s*\\((.*?):(\\d+):(\\d+)\\)$",
            //     "message": 1,
            //     "file": 2,
            //     "line": 3,
            //     "column": 4
            //   }
            // }
          }
        ]
      }

- Open a Voila file from the project (i.e. `demo/some_file.vl`) and verify it
  by using the keyboard shortcut `Ctrl+Shift+B` or via `Tasks: Run Build Task` 
  from VSCode's command palette.
- Voila is executed in VSCode's terminal, which can be configured as described
  in the previous section about the Code Runner plugin (i.e. by adjusting
  `terminal.integrated.shell`)
- A *problem matcher* can be used to parse Voila's output and highlight failing
  assertions via squiggly lines (but, as far as I know, not to highlight the
  output itself). Commented code above is from a partially successful 
  experiment, but: only the first word in the offending line was 
  highlighted (for proper highlighting, Voila errors need to contain start and
  end position); due to incomplete error back-translation, Voila errors 
  sometimes lack position information.

### 3. Windows: Using AutoHotkey and MSYS2

- Install [MSYS2](http://www.msys2.org/)
- Install [AutoHotkey](https://autohotkey.com/) (v1 should work, not sure about
  v2)
- Open VSCode and an MSYS2 terminal (e.g. `MSYS2 MinGW 64-bit`) and place the 
  windows side-by-side (e.g. using `Win+Left`/`Win+Right`)
- Focus the terminal:
    - Let's assume the Voila source directory is the current directory
    - Create an environment variable pointing to Voila's executable. E.g.

          VOILA_CMD='/voila/misc/nailgun/voila.bat ng=true'

      for using Nailgun. It is expected that a Voila file can be verified by
      running
      
          $VOILA_CMD -i /absolute/path/to/some/file.vl

    - However Voila is run, ensure that it colours its output (errors) by
      passing the Logback configuration `./conf/logback-color.xml` to the JVM
      at start-up
    - Execute `source ./misc/vscode/demo-env-win/setup.bash`
    - The terminal prompt should have changed, and it should now be possible
      to verify a Voila file by executing `voila path/to/some/file.vl` 
      (absolute and relative paths should work)
- Load the script `./misc/vscode/demo-env-win/setup.ahk` into AutoHotkey
- The following keyboard shortcuts should now work:
    - In VSCode, pressing `F5` should verify the currently open Voila file in
      the open MSYS2 terminal
    - Pressing `Win+Alt+Left` should horizontally enlarge VSCode and shrink the
      terminal, and `Win+Alt+Right` should have the opposite effect
    - Pressing `Win+Ctrl+f` should make VSCode and MSYS2 fullscreen by removing
      decorational border/frame elements (press again to undo)
    - Pressing `Win+Alt+Up` should maximise VSCode and thus hide the terminal
      (press again to undo). This might only properly cover the screen if
      VSCode is in fullscreen mode (`Win+Ctrl+f`).
- For the perfect demo mode:
    - Hide several VSCode GUI elements via the following settings:

          "window.menuBarVisibility": "toggle",
          "workbench.activityBar.visible": false,
          "editor.minimap.enabled": false,
          "workbench.statusBar.visible": false,

    - Hide VSCode's tab bar by opening the developer tools
      (`Help` -> `Toggle Developer Tools`) and running the following
      in the Javascript console:
      `$$(".editor .content .container .title")[0].style.display = "none"`
    - Hide the scrollbar of the MSYS2 terminal via 
      `Options` -> `Window` -> `Scrollbar` -> `None`
    - Use `Win+Ctrl+f` to make VSCode and the MSYS2 terminal fullscreen

## Nailgun

- To reduce startup time, consider running Voila via 
  [Nailgun](https://github.com/facebook/nailgun)
- The directory `voila/misc/nailgun` contains an older version of the Nailgun
  server (`nailgun-server-0.9.1.jar`), the Nailgun client for Windows
  (`ng.exe`) and two Windows batch files for starting Voila as a Nailgun 
  daemon (`voila-ng-daemon.bat`) and for verifying a file through the daemon
  (`voila.bat`)
- Execute `voila-ng-daemon.bat` to start the Voila daemon. 
  Have a look at the batch file to see possible options: in particular, the
  options `jar` and `logback`.
- Configure the Code runner as follows to verify Voila files via the Voila 
  daemon:

      "code-runner.executorMapByFileExtension": {
        ".vl": "voila/misc/nailgun/voila.bat ng=true -i $fullFileName"
      },
