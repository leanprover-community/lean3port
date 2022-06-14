/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for showing that a type has decidable equality.
-/
prelude
import Leanbin.Init.Meta.ContradictionTactic
import Leanbin.Init.Meta.ConstructorTactic
import Leanbin.Init.Meta.InjectionTactic
import Leanbin.Init.Meta.RelationTactics
import Leanbin.Init.Meta.RecUtil
import Leanbin.Init.Meta.Interactive

namespace Tactic

open Expr Environment List

-- Retrieve the name of the type we are building a decidable equality proof for.
private unsafe def get_dec_eq_type_name : tactic Name :=
  (do
      let pi x1 i1 d1 (pi x2 i2 d2 b) ← target >>= whnf
      let const n ls ← return (get_app_fn b)
      when (n ≠ `decidable) failed
      let const I ls ← return (get_app_fn d1)
      return I) <|>
    fail "mk_dec_eq_instance tactic failed, target type is expected to be of the form (decidable_eq ...)"

-- Extract (lhs, rhs) from a goal (decidable (lhs = rhs))
private unsafe def get_lhs_rhs : tactic (expr × expr) := do
  let app dec lhs_eq_rhs ← target | fail "mk_dec_eq_instance failed, unexpected case"
  match_eq lhs_eq_rhs

private unsafe def find_next_target : List expr → List expr → tactic (expr × expr)
  | t :: ts, r :: rs => if t = r then find_next_target ts rs else return (t, r)
  | l1, l2 => failed

-- Create an inhabitant of (decidable (lhs = rhs))
private unsafe def mk_dec_eq_for (lhs : expr) (rhs : expr) : tactic expr := do
  let lhs_type ← infer_type lhs
  let dec_type ← mk_app `decidable_eq [lhs_type] >>= whnf
  (do
        let inst ← mk_instance dec_type
        return <| inst lhs rhs) <|>
      do
      let f ← pp dec_type
      fail <| to_fmt "mk_dec_eq_instance failed, failed to generate instance for" ++ format.nest 2 (format.line ++ f)

private unsafe def apply_eq_of_heq (h : expr) : tactic Unit := do
  let pr ← mk_app `eq_of_heq [h]
  let ty ← infer_type pr
  assertv `h' ty pr >> skip

-- ././Mathport/Syntax/Translate/Basic.lean:914:4: warning: unsupported (TODO): `[tacs]
-- Target is of the form (decidable (C ... = C ...)) where C is a constructor
private unsafe def dec_eq_same_constructor : Name → Name → Nat → tactic Unit
  | I_name, F_name, num_rec => do
    let (lhs, rhs) ← get_lhs_rhs
    (-- Try easy case first, where the proof is just reflexivity
              unify
              lhs rhs >>
            right) >>
          reflexivity <|>
        do
        let lhs_list := get_app_args lhs
        let rhs_list := get_app_args rhs
        when (length lhs_list ≠ length rhs_list)
            (fail "mk_dec_eq_instance failed, constructor applications have different number of arguments")
        let (lhs_arg, rhs_arg) ← find_next_target lhs_list rhs_list
        let rec ← is_type_app_of lhs_arg I_name
        let inst ←
          if rec then do
              let inst_fn ← mk_brec_on_rec_value F_name num_rec
              return <| app inst_fn rhs_arg
            else do
              mk_dec_eq_for lhs_arg rhs_arg
        sorry
        (-- discharge first (positive) case by recursion
              intro1 >>=
              subst) >>
            dec_eq_same_constructor I_name F_name (if rec then num_rec + 1 else num_rec)
        -- discharge second (negative) case by contradiction
          intro1
        left
        -- decidable.is_false
            intro1 >>=
            injection
        intros
        contradiction <|> do
            let lc ← local_context
            lc fun h => try (apply_eq_of_heq h) <|> skip
            contradiction
        return ()

-- Easy case: target is of the form (decidable (C_1 ... = C_2 ...)) where C_1 and C_2 are distinct constructors
private unsafe def dec_eq_diff_constructor : tactic Unit :=
  (left >> intron 1) >> contradiction

/- This tactic is invoked for each case of decidable_eq. There n^2 cases, where n is the number
   of constructors. -/
private unsafe def dec_eq_case_2 (I_name : Name) (F_name : Name) : tactic Unit := do
  let (lhs, rhs) ← get_lhs_rhs
  let lhs_fn := get_app_fn lhs
  let rhs_fn := get_app_fn rhs
  if lhs_fn = rhs_fn then dec_eq_same_constructor I_name F_name 0 else dec_eq_diff_constructor

private unsafe def dec_eq_case_1 (I_name : Name) (F_name : Name) : tactic Unit :=
  (intro `w >>= cases) >> all_goals' (dec_eq_case_2 I_name F_name)

unsafe def mk_dec_eq_instance_core : tactic Unit := do
  let I_name ← get_dec_eq_type_name
  let env ← get_env
  let v_name := `_v
  let F_name := `_F
  let num_indices := inductive_num_indices env I_name
  let idx_names :=
    List.map (fun p : Name × Nat => mkNumName p.fst p.snd)
      (List.zipₓ (List.repeat `idx num_indices) (List.iota num_indices))
  -- Use brec_on if type is recursive.
      -- We store the functional in the variable F.
      if is_recursive env I_name then
      intro1 >>= fun x => induction x (idx_names ++ [v_name, F_name]) (some <| mkStrName I_name "brec_on") >> return ()
    else intro v_name >> return ()
  -- Apply cases to first element of type (I ...)
        get_local
        v_name >>=
      cases
  all_goals' (dec_eq_case_1 I_name F_name)

-- ././Mathport/Syntax/Translate/Basic.lean:914:4: warning: unsupported (TODO): `[tacs]
unsafe def mk_dec_eq_instance : tactic Unit := do
  let env ← get_env
  let pi x1 i1 d1 (pi x2 i2 d2 b) ← target >>= whnf
  let const I_name ls ← return (get_app_fn d1)
  when (is_ginductive env I_name ∧ ¬is_inductive env I_name) <| do
      let d1' ← whnf d1
      let app I_basic_const I_idx ← return d1'
      let I_idx_type ← infer_type I_idx
      let new_goal ← to_expr (pquote.1 (∀ _idx : %%ₓI_idx_type, DecidableEq ((%%ₓI_basic_const) _idx)))
      assert `_basic_dec_eq new_goal
      swap
      sorry
      intro1
      return ()
  mk_dec_eq_instance_core

unsafe instance binder_info.has_decidable_eq : DecidableEq BinderInfo := by
  run_tac
    mk_dec_eq_instance

@[derive_handler]
unsafe def decidable_eq_derive_handler :=
  instance_derive_handler `` DecidableEq tactic.mk_dec_eq_instance

end Tactic

