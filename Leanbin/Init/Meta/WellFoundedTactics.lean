/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Default
import Leanbin.Init.Data.Sigma.Lex
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Data.List.Instances
import Leanbin.Init.Data.List.Qsort

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. 
-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.lt_add_of_zero_lt_left (a b : Nat) (h : 0 < b) : a < a + b :=
  show a + 0 < a + b by
    apply Nat.add_lt_add_leftₓ
    assumption

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.zero_lt_one_add (a : Nat) : 0 < 1 + a :=
  suffices 0 < a + 1 by
    simp [← Nat.add_comm]
    assumption
  Nat.zero_lt_succₓ _

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.lt_add_rightₓ (a b c : Nat) : a < b → a < b + c := fun h => lt_of_lt_of_leₓ h (Nat.le_add_rightₓ _ _)

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.lt_add_left (a b c : Nat) : a < b → a < c + b := fun h => lt_of_lt_of_leₓ h (Nat.le_add_leftₓ _ _)

protected def PSum.Alt.sizeof.{u, v} {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] : PSum α β → ℕ
  | PSum.inl a => sizeof a
  | PSum.inr b => sizeof b

@[reducible]
protected def PSum.hasSizeofAlt.{u, v} (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (PSum α β) :=
  ⟨PSum.Alt.sizeof⟩

namespace WellFoundedTactics

open Tactic

def IdTag.wf : Unit :=
  ()

unsafe def mk_alt_sizeof : expr → expr
  | expr.app (expr.app (expr.app (expr.app (expr.const `` PSum.hasSizeof l) α) β) iα) iβ =>
    (expr.const `` PSum.hasSizeofAlt l : expr) α β iα (mk_alt_sizeof iβ)
  | e => e

unsafe def default_rel_tac (e : expr) (eqns : List expr) : tactic Unit := do
  let tgt ← target
  let rel ← mk_instance tgt
  exact <|
      match e, rel with
      | expr.local_const _ (Name.mk_string "_mutual" _) _ _, expr.app (e@(quote.1 (@hasWellFoundedOfHasSizeof _))) sz =>
        e (mk_alt_sizeof sz)
      | _, _ => rel

private unsafe def clear_wf_rec_goal_aux : List expr → tactic Unit
  | [] => return ()
  | h :: hs => clear_wf_rec_goal_aux hs >> try (guardₓ (h.local_pp_name.is_internal || h.is_aux_decl) >> clear h)

unsafe def clear_internals : tactic Unit :=
  local_context >>= clear_wf_rec_goal_aux

unsafe def unfold_wf_rel : tactic Unit :=
  dunfold_target [`` HasWellFounded.R] { failIfUnchanged := false }

unsafe def is_psigma_mk : expr → tactic (expr × expr)
  | quote.1 (PSigma.mk (%%ₓa) (%%ₓb)) => return (a, b)
  | _ => failed

-- ./././Mathport/Syntax/Translate/Basic.lean:1052:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1052:4: warning: unsupported (TODO): `[tacs]
unsafe def process_lex : tactic Unit → tactic Unit
  | tac => do
    let t ← target >>= whnf
    if t `psigma.lex 6 then
        let a := t
        let b := t
        do
        let (a₁, a₂) ← is_psigma_mk a
        let (b₁, b₂) ← is_psigma_mk b
        (is_def_eq a₁ b₁ >> sorry) >> process_lex tac <|> sorry >> tac
      else tac

private unsafe def unfold_sizeof_measure : tactic Unit :=
  dunfold_target [`` SizeofMeasure, `` Measureₓ, `` InvImage] { failIfUnchanged := false }

private unsafe def add_simps : simp_lemmas → List Name → tactic simp_lemmas
  | s, [] => return s
  | s, n :: ns => do
    let s' ← s.add_simp n false
    add_simps s' ns

private unsafe def collect_sizeof_lemmas (e : expr) : tactic simp_lemmas :=
  (e.mfold simp_lemmas.mk) fun c d s =>
    if c.is_constant then
      match c.const_name with
      | Name.mk_string "sizeof" p => do
        let eqns ← get_eqn_lemmas_for true c.const_name
        add_simps s eqns
      | _ => return s
    else return s

-- ./././Mathport/Syntax/Translate/Basic.lean:1052:4: warning: unsupported (TODO): `[tacs]
private unsafe def unfold_sizeof_loop : tactic Unit := do
  dunfold_target [`` sizeof, `` SizeOf.sizeof] { failIfUnchanged := ff }
  let S ← target >>= collect_sizeof_lemmas
  simp_target S >> unfold_sizeof_loop <|> try sorry

unsafe def unfold_sizeof : tactic Unit :=
  unfold_sizeof_measure >> unfold_sizeof_loop

/- The following section should be removed as soon as we implement the
   algebraic normalizer. -/
section SimpleDecTac

open Tactic Expr

private unsafe def collect_add_args : expr → List expr
  | quote.1 ((%%ₓa) + %%ₓb) => collect_add_args a ++ collect_add_args b
  | e => [e]

private unsafe def mk_nat_add : List expr → tactic expr
  | [] => to_expr (pquote.1 0)
  | [a] => return a
  | a :: as => do
    let rs ← mk_nat_add as
    to_expr (pquote.1 ((%%ₓa) + %%ₓrs))

private unsafe def mk_nat_add_add : List expr → List expr → tactic expr
  | [], b => mk_nat_add b
  | a, [] => mk_nat_add a
  | a, b => do
    let t ← mk_nat_add a
    let s ← mk_nat_add b
    to_expr (pquote.1 ((%%ₓt) + %%ₓs))

private unsafe def get_add_fn (e : expr) : expr :=
  if is_napp_of e `has_add.add 4 then e.app_fn.app_fn else e

private unsafe def prove_eq_by_perm (a b : expr) : tactic expr :=
  is_def_eq a b >> to_expr (pquote.1 (Eq.refl (%%ₓa))) <|>
    perm_ac (get_add_fn a) (quote.1 Nat.add_assoc) (quote.1 Nat.add_comm) a b

private unsafe def num_small_lt (a b : expr) : Bool :=
  if a = b then false
  else if is_napp_of a `has_one.one 2 then true else if is_napp_of b `has_one.one 2 then false else a.lt b

private unsafe def sort_args (args : List expr) : List expr :=
  args.qsort num_small_lt

private def tagged_proof.wf : Unit :=
  ()

-- ./././Mathport/Syntax/Translate/Basic.lean:1052:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1052:4: warning: unsupported (TODO): `[tacs]
unsafe def cancel_nat_add_lt : tactic Unit := do
  let quote.1 ((%%ₓlhs) < %%ₓrhs) ← target
  let ty ← infer_type lhs >>= whnf
  guardₓ (ty = quote.1 Nat)
  let lhs_args := collect_add_args lhs
  let rhs_args := collect_add_args rhs
  let common := lhs_args.bagInter rhs_args
  if common = [] then return ()
    else do
      let lhs_rest := lhs_args common
      let rhs_rest := rhs_args common
      let new_lhs ← mk_nat_add_add common (sort_args lhs_rest)
      let new_rhs ← mk_nat_add_add common (sort_args rhs_rest)
      let lhs_pr ← prove_eq_by_perm lhs new_lhs
      let rhs_pr ← prove_eq_by_perm rhs new_rhs
      let target_pr ← to_expr (pquote.1 (congr (congr_arg (· < ·) (%%ₓlhs_pr)) (%%ₓrhs_pr)))
      let new_target ← to_expr (pquote.1 ((%%ₓnew_lhs) < %%ₓnew_rhs))
      replace_target new_target target_pr `` id_tag.wf
      sorry <|> sorry

unsafe def check_target_is_value_lt : tactic Unit := do
  let quote.1 ((%%ₓlhs) < %%ₓrhs) ← target
  guardₓ lhs

-- ./././Mathport/Syntax/Translate/Basic.lean:1052:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1052:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1052:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1052:4: warning: unsupported (TODO): `[tacs]
unsafe def trivial_nat_lt : tactic Unit :=
  comp_val <|>
    sorry <|>
      sorry <|>
        assumption <|>
          (do
              check_target_is_value_lt
              sorry >> trivial_nat_lt <|> sorry >> trivial_nat_lt) <|>
            failed

end SimpleDecTac

unsafe def default_dec_tac : tactic Unit :=
  abstract <| do
    clear_internals
    unfold_wf_rel
    -- The next line was adapted from code in mathlib by Scott Morrison.
          -- Because `unfold_sizeof` could actually discharge the goal, add a test
          -- using `done` to detect this.
          process_lex
          (unfold_sizeof >>
            (done <|>
              cancel_nat_add_lt >>
                trivial_nat_lt)) <|>-- Clean up the goal state but not too much before printing the error
          unfold_sizeof >>
          fail "default_dec_tac failed"

end WellFoundedTactics

/-- Argument for using_well_founded

  The tactic `rel_tac` has to synthesize an element of type (has_well_founded A).
  The two arguments are: a local representing the function being defined by well
  founded recursion, and a list of recursive equations.
  The equations can be used to decide which well founded relation should be used.

  The tactic `dec_tac` has to synthesize decreasing proofs.
-/
unsafe structure well_founded_tactics where
  rel_tac : expr → List expr → tactic Unit := well_founded_tactics.default_rel_tac
  dec_tac : tactic Unit := well_founded_tactics.default_dec_tac

unsafe def well_founded_tactics.default : well_founded_tactics where

