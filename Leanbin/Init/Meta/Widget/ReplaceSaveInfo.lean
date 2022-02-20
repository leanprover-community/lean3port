/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import Leanbin.Init.Meta.Widget.InteractiveExpr

unsafe def tactic.save_info_with_widgets (p : Pos) : tactic Unit := do
  let s ← tactic.read
  tactic.save_info_thunk p fun _ => tactic_state.to_format s
  tactic.save_widget p widget.tactic_state_widget

attribute [implementedBy tactic.save_info_with_widgets] tactic.save_info

