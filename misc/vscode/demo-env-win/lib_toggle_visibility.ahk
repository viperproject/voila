;; Toggles the visibility of the window belonging to the given process proc.
;; It is assumed that the window is initially visible.
toggleVisibility(proc) {
  static hidden := []

  MsgBox, % hidden[proc]

  if !hidden[proc] {
    WinHide %proc%
  } else {
    WinShow %proc%
  }

  hidden[proc] := !hidden[proc]

  return
}
