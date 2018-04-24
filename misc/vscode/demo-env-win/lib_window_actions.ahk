;; leftProc and rightProc are expected to denote processes whose windows are
;; horizontally adjacent/snapped to each other, with leftProc on the left
;; if rightProc.
;; This function then shifts the split line of their windows (their common 
;; horizontal border) by the specified delta. I.e. one window is enlarged
;; by delta while the other is shrunken.
moveWindowSplitBy(leftProc, rightProc, delta) {
  WinGetPos, vscCurPosX, , vscCurWidth, , %leftProc%
  WinGetPos, ttyCurPosX, , ttyCurWidth, , %rightProc%
  
  if (0 < delta) {
    WinMove %leftProc%, , , , vscCurWidth + delta,
    WinMove %rightProc%, , ttyCurPosX + delta, , ttyCurWidth - delta, 
  } else {
    WinMove %rightProc%, , ttyCurPosX + delta, , ttyCurWidth - delta, 
    WinMove %leftProc%, , , , vscCurWidth + delta, 
  }

  return
}





;; The next functions are based on the borderless fullscreen script described here:
;; https://autohotkey.com/boards/viewtopic.php?p=123166#p123166

getMonitorProperties(proc, ByRef left, ByRef top, ByRef right, ByRef bottom) {
  static MONITOR_DEFAULTTONEAREST := 0x00000002

  hMon := DllCall("User32\MonitorFromWindow", "Ptr", proc, "UInt", MONITOR_DEFAULTTONEAREST)
  VarSetCapacity(monInfo, 40), NumPut(40, monInfo, 0, "UInt")
  DllCall("User32\GetMonitorInfo", "Ptr", hMon, "Ptr", &monInfo)

  left := NumGet(monInfo,  4, "Int")
  top := NumGet(monInfo,  8, "Int")
  right := NumGet(monInfo, 12, "Int")
  bottom := NumGet(monInfo, 16, "Int")

  return
}

toggleWindowPseudoFullscreen(proc, left, top, width, height) {
  static WS_CAPTION               := 0x00C00000
  static WS_SIZEBOX               := 0x00040000
  static windowStyle              := WS_CAPTION|WS_SIZEBOX
  static state := []

  WinGet, currentStyle, Style, %proc% ; Get window style

  if (currentStyle & windowStyle) { ; If not pseudo-fullscreen
    state[proc, "style"] := currentStyle & windowStyle ; Store existing style
    WinGet, isMaxed, MinMax, %proc% ; Get/store whether the window is maximised
    
    if (state[proc, "maxed"] := isMaxed = 1 ? true : false)
      WinRestore, %proc%
    
    ; Obtain and save current window size and location
    WinGetPos, currentX, currentY, currentWidth, currentHeight, %proc%
    state[proc, "x"] := currentX
    state[proc, "y"] := currentY
    state[proc, "width"] := currentWidth
    state[proc, "height"] := currentHeight

    WinSet, Style, % -windowStyle, %proc% ; Remove borders
    WinMove, %proc%,, left, top, width, height ; Relocate and resize
  } else if state[proc] { ; If pseudo-fullscreen
    WinSet, Style, % "+" state[proc].style, %proc% ; Reapply borders
    
    ; Restore original size and location
    WinMove, %proc%,, state[proc].x
                    , state[proc].y
                    , state[proc].width
                    , state[proc].height 
    
    if (state[proc].maxed) ; Maximise if required
      WinMaximize, %proc%
    
    state.Delete(proc)
  }
}

toggleSplitWindowsPseudoFullscreen(leftProc, rightProc, resplit := false) {
  ;; NOTE: It is assumed that leftProc and rightProc are displayed on the same
  ;;       monitor!

  getMonitorProperties(leftProc, monLeft, monTop, monRight, monBottom)

  ;; Multi-line statements look rather weird in AHK
  ;; See https://www.autohotkey.com/docs/Scripts.htm#continuation

  toggleWindowPseudoFullscreen(leftProc
      , monLeft, monTop
      , (monRight - monLeft) / 2, monBottom - monTop)

  toggleWindowPseudoFullscreen(rightProc
      , (monRight - monLeft) / 2, monTop
      , (monRight - monLeft) / 2, monBottom - monTop)
}



;; Maximises proc.
;; Currently only works if proc has been made borderless via toggleSplitWindowsPseudoFullscreen.
;; Otherwise, the "maximised" proc won't actually cover the whole screen.
togglePseudoWindowMaximization(proc) {
  static state := []

  if (state[proc]) {
    ; MsgBox % state.width

    WinMove, %proc%, , state[proc].x, state[proc].y, state[proc].width, state[proc].height

    state.Delete(proc)
  } else {
    WinGetPos, x, y, width, height, %proc%
    
    state[proc, "x"] := x
    state[proc, "y"] := y
    state[proc, "width"] := width
    state[proc, "height"] := height

    getMonitorProperties(proc, monLeft, monTop, monRight, monBottom)

    ; MsgBox % "monLeft = " . monLeft
    ; MsgBox % "monTop = " . monTop
    ; MsgBox % "monRight = " . monRight
    ; MsgBox % "monBottom = " . monBottom
    ; MsgBox % "x = " . x
    ; MsgBox % "y = " . y

    ; ;; See https://autohotkey.com/docs/commands/SysGet.htm
    ; ;; Unfortunately, none of them appear to yield a height that corresponds
    ; ;; to the maximised height of a VSCode window
    ; SysGet, maximizedWidth, 61 ; SM_CXMAXIMIZED
    ; ; SysGet, maximizedHeight, 62 ; SM_CYMAXIMIZED ;; Slightly too large
    ; ; SysGet, maximizedHeight, 17 ; SM_CYFULLSCREEN
    ; ; SysGet, maximizedHeight, 60 ; SM_CYMAXTRACK
    ; ; SysGet, maximizedHeight, 1 ; SM_CYSCREEN
    ; ; SysGet, maximizedHeight, 79 ; SM_CYVIRTUALSCREEN
    ; maximizedHeight := height

    maximizedWidth := monRight - monLeft ; - x
    maximizedHeight := monBottom - monTop ; - y

    ; MsgBox, % maximizedWidth
    ; MsgBox, % maximizedHeight

    WinMove %proc%, , , , maximizedWidth, maximizedHeight
  }
}
