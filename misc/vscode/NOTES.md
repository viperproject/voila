Custom settings:  
  
  "code-runner.executorMapByFileExtension": {
    ".vl": "voila.bat ng=true -i $fullFileName"
  },
  "code-runner.clearPreviousOutput": true,
  "code-runner.showExecutionMessage": false,
  "code-runner.ignoreSelection": true,
  "code-runner.enableAppInsights": false,


  "editor.tokenColorCustomizations": {
    "[Default Dark+]": {
      "textMateRules": [
        {
          "scope": "keyword.control.atomicity-modifiers.voila",
          "settings": {
            // "foreground": "#89BDFF"
            "foreground": "#AE81FF"
          }
        },
        {
          "scope": "keyword.control.toplevel.voila",
          "settings": {
            "foreground": "#A6E22E"
          }
        },
        // {
        //   "scope": "storage.type",
        //   "settings": {
        //     "foreground": "#66D9EF"
        //   }
        // }
      ]
    }

    // "[Default Dark+]": {
    //   "keywords": "#89BDFF"
    // }
  }