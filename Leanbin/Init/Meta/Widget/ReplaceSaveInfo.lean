/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers

! This file was ported from Lean 3 source module init.meta.widget.replace_save_info
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Widget.InteractiveExpr

unsafe def tactic.save_info_with_widgets (p : Pos) : tactic Unit := do
  let s ← tactic.read
  tactic.save_info_thunk p fun _ => tactic_state.to_format s
  tactic.save_widget p widget.tactic_state_widget
#align tactic.save_info_with_widgets tactic.save_info_with_widgets

attribute [implemented_by tactic.save_info_with_widgets] tactic.save_info

