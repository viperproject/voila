extractCurrentFileFromWindowTitle( vscProc
                                 , ByRef basename
                                 , ByRef extension
                                 , ByRef hasUnsavedChanges) {

  WinGetTitle, title, %vscProc%

  ; VSCode's window title is expected to start with a relative filename that
  ; has an extension, potentially preceded by the black circle (●, U+25CF) 
  ; that marks a file as having unsaved changes.
  RegExMatch(title, "\s*(\x{25CF})?\s*(.+)\.(.+?) .*", matches)
  hasUnsavedChanges := matches1
  basename := matches2
  extension := matches3
  
  ; MsgBox, % "hasUnsavedChanges = '" . hasUnsavedChanges . "'`n" 
  ;         . "base =  '" . basename . "'`n" 
  ;         . "ext = '" . extension . "'"

  return
}

doWithCurrentFileInTerminal( vscProc
                           , ttyProc
                           , expectedExtension
                           , fnCommand
                           , saveChanges := false
                           , clear := false) {

  if (!IsFunc(fnCommand)) {
    MsgBox, 16
          , % "Error calling doWithCurrentFileInTerminal"
          , % "Parameter fnCommand must denote a function"
    
    return
  }

  extractCurrentFileFromWindowTitle(vscProc, basename, extension, hasUnsavedChanges)

  if (hasUnsavedChanges and saveChanges) {
    ; Save current file by sending Ctrl+s
    Send ^s
    Sleep 100
  }

  if (expectedExtension and extension != expectedExtension) {
    return
  }

  WinActivate, %ttyProc%
  WinWaitActive, %ttyProc%

  if (clear) {
    Send {Text}clear`n
  }

  %fnCommand%(basename, extension)
  
  return
}
