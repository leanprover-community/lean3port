/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner

! This file was ported from Lean 3 source module init.meta.async_tactic
! leanprover-community/mathlib commit 6e4c67e71566ea02dd0d5e50b3b92312d20ba681
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Meta.InstanceCache

namespace Tactic

private unsafe def report {α} (s : tactic_state) : Option (Unit → format) → α
  | some fmt => undefined_core <| format.to_string <| fmt () ++ format.line ++ to_fmt s
  | none => undefined_core "silent failure"
#align tactic.report tactic.report

private unsafe def run_or_fail {α} (s : tactic_state) (tac : tactic α) : α :=
  match tac s with
  | result.success a s => a
  | result.exception fmt _ s' => report s' fmt
#align tactic.run_or_fail tactic.run_or_fail

unsafe def run_async {α : Type} (tac : tactic α) : tactic (task α) := do
  let s ← read
  return <|
      task.delay fun _ =>
        match tac s with
        | result.success a s => a
        | result.exception fmt _ s' => report s' fmt
#align tactic.run_async tactic.run_async

unsafe def prove_goal_async (tac : tactic Unit) : tactic Unit := do
  let ctx ← local_context
  unfreezing (revert_lst ctx)
  let tgt ← target
  let tgt ← instantiate_mvars tgt
  let env ← get_env
  let tgt ← return <| env.unfold_untrusted_macros tgt
  when tgt (fail "goal contains metavariables")
  let params ← return tgt.collect_univ_params
  let lemma_name ← new_aux_decl_name
  let proof ←
    run_async do
        let goal_meta ← mk_meta_var tgt
        set_goals [goal_meta]
        ctx fun c => unfreezing (intro c)
        tac
        let proof ← instantiate_mvars goal_meta
        let proof ← return <| env.unfold_untrusted_macros proof
        when proof <| fail "async proof failed: contains metavariables"
        return proof
  add_decl <| declaration.thm lemma_name params tgt proof
  exact (expr.const lemma_name (params level.param))
#align tactic.prove_goal_async tactic.prove_goal_async

namespace Interactive

open Interactive.Types

/-- Proves the first goal asynchronously as a separate lemma. -/
unsafe def async (tac : itactic) : tactic Unit :=
  prove_goal_async tac
#align tactic.interactive.async tactic.interactive.async

end Interactive

end Tactic

