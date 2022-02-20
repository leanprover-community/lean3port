/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Function

namespace Tactic

open Expr

private unsafe def relation_tactic (md : Transparency) (op_for : environment → Name → Option Name)
    (tac_name : Stringₓ) : tactic Unit := do
  let tgt ← target >>= instantiate_mvars
  let env ← get_env
  let r := get_app_fn tgt
  match op_for env (const_name r) with
    | some refl => do
      let r ← mk_const refl
      apply_core r { md, NewGoals := new_goals.non_dep_only } >> return ()
    | none => fail <| tac_name ++ " tactic failed, target is not a relation application with the expected property."

unsafe def reflexivity (md := semireducible) : tactic Unit :=
  relation_tactic md environment.refl_for "reflexivity"

unsafe def symmetry (md := semireducible) : tactic Unit :=
  relation_tactic md environment.symm_for "symmetry"

unsafe def transitivity (md := semireducible) : tactic Unit :=
  relation_tactic md environment.trans_for "transitivity"

unsafe def relation_lhs_rhs (e : expr) : tactic (Name × expr × expr) := do
  let const c _ ← return e.get_app_fn
  let env ← get_env
  let some (arity, lhs_pos, rhs_pos) ← return <| env.relation_info c
  let args ← return <| get_app_args e
  guardₓ (args = arity)
  let some lhs ← return <| args.nth lhs_pos
  let some rhs ← return <| args.nth rhs_pos
  return (c, lhs, rhs)

/-- If the main target has the form `r lhs rhs`, then return `(r,lhs,rhs)`. -/
unsafe def target_lhs_rhs : tactic (Name × expr × expr) :=
  target >>= relation_lhs_rhs

/-- Try to apply subst exhaustively -/
unsafe def subst_vars : tactic Unit :=
  focus1 <| iterate (any_hyp subst) >> try (reflexivity reducible)

end Tactic

