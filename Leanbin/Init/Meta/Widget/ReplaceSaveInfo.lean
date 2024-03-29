/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import Init.Meta.Widget.InteractiveExpr

#align_import init.meta.widget.replace_save_info from "leanprover-community/lean"@"cacc7c8aa0f97341f8b50ae48c3069429f6c21de"

unsafe def tactic.save_info_with_widgets (p : Pos) : tactic Unit := do
  let s ← tactic.read
  tactic.save_info_thunk p fun _ => tactic_state.to_format s
  tactic.save_widget p widget.tactic_state_widget
#align tactic.save_info_with_widgets tactic.save_info_with_widgets

attribute [implemented_by tactic.save_info_with_widgets] tactic.save_info

