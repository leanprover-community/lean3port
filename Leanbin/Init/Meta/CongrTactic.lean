/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

! This file was ported from Lean 3 source module init.meta.congr_tactic
! leanprover-community/lean commit c0792dde6a5c738ec01ca51039622828c43895d3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.CongrLemma
import Leanbin.Init.Meta.RelationTactics
import Leanbin.Init.Function

namespace Tactic

unsafe def apply_congr_core (clemma : congr_lemma) : tactic Unit := do
  assert `H_congr_lemma clemma
  exact clemma
  get_local `H_congr_lemma >>= apply
  all_goals' do
      try (applyc `heq_of_eq)
      get_local `H_congr_lemma >>= clear
#align tactic.apply_congr_core tactic.apply_congr_core

unsafe def apply_eq_congr_core (tgt : expr) : tactic Unit := do
  let (lhs, rhs) ← match_eq tgt
  guard lhs
  let clemma ← mk_specialized_congr_lemma lhs
  apply_congr_core clemma
#align tactic.apply_eq_congr_core tactic.apply_eq_congr_core

unsafe def apply_heq_congr_core : tactic Unit := do
  try (applyc `eq_of_heq)
  let (α, lhs, β, rhs) ← target >>= match_heq
  guard lhs
  let clemma ← mk_hcongr_lemma lhs.get_app_fn lhs.get_app_num_args
  apply_congr_core clemma
#align tactic.apply_heq_congr_core tactic.apply_heq_congr_core

unsafe def congr_core : tactic Unit := do
  let tgt ← target
  apply_eq_congr_core tgt <|> apply_heq_congr_core <|> fail "congr tactic failed"
#align tactic.congr_core tactic.congr_core

unsafe def congr : tactic Unit := do
  focus1 ((try assumption >> congr_core) >> all_goals' (try reflexivity >> try congr))
#align tactic.congr tactic.congr

end Tactic

