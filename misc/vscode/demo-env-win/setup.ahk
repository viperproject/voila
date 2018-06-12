#NoEnv  ; Recommended for performance and compatibility with future AutoHotkey releases.
#Warn  ; Enable warnings to assist with detecting common errors.
SendMode Input  ; Recommended for new scripts due to its superior speed and reliability.
SetWorkingDir %A_ScriptDir%  ; Ensures a consistent starting directory.
SetWinDelay, -1
SetTitleMatchMode RegEx

; Set directory from where to include files
#Include %A_ScriptDir%

; Actual includes
#Include lib_window_actions.ahk
#Include lib_toggle_visibility.ahk
#Include lib_current_file_actions.ahk

global vscProc := "ahk_exe i)\\Code.*\.exe$"
global ttyProc := "ahk_exe i)\\mintty\.exe$"
global epProc := "ahk_exe EpicPen.exe"

verifyVoilaFile(basename, extension) {
  Send {Text}voila %basename%.%extension%`n

  return
}

^!r::Reload ; Assign Ctrl+Alt+R as a hotkey to restart the script.

#!Left:: moveWindowSplitBy(vscProc, ttyProc, -300) ; Win+Alt+Left
#!Right:: moveWindowSplitBy(vscProc, ttyProc, 300) ; Win+Alt+Right

#^f::toggleSplitWindowsPseudoFullscreen(vscProc, ttyProc, false) ; Win+Ctrl+f

; #if (WinActive(epProc))
  #space:: toggleVisibility(epProc)

#if (WinActive(vscProc))
  F5:: doWithCurrentFileInTerminal(vscProc, ttyProc, "vl", Func("verifyVoilaFile"), true, true)
  #!Up:: togglePseudoWindowMaximization(vscProc) ; Win+Alt+Up