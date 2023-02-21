/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Converter monad for building simplifiers.

! This file was ported from Lean 3 source module init.meta.converter.conv
! leanprover-community/mathlib commit e83eca1fc5eda5ec3e0926a6913e02d9a574bf9e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.SimpTactic
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Meta.CongrLemma
import Leanbin.Init.Meta.MatchTactic

open Tactic

def Tactic.IdTag.conv : Unit :=
  ()
#align tactic.id_tag.conv Tactic.IdTag.conv

universe u

/--
`conv α` is a tactic for discharging goals of the form `lhs ~ rhs` for some relation `~` (usually equality) and fixed lhs, rhs.
Known in the literature as a __conversion__ tactic.
So for example, if one had the lemma `p : x = y`, then the conversion for `p` would be one that solves `p`.
-/
unsafe def conv (α : Type u) :=
  tactic α
#align conv conv

unsafe instance : Monad conv := by dsimp only [conv] <;> infer_instance

unsafe instance : MonadFail conv := by dsimp only [conv] <;> infer_instance

unsafe instance : Alternative conv := by dsimp only [conv] <;> infer_instance

namespace Conv

/--
Applies the conversion `c`. Returns `(rhs,p)` where `p : r lhs rhs`. Throws away the return value of `c`.-/
unsafe def convert (c : conv Unit) (lhs : expr) (rel : Name := `eq) : tactic (expr × expr) := do
  let lhs_type ← infer_type lhs
  let rhs ← mk_meta_var lhs_type
  let new_target ← mk_app Rel [lhs, rhs]
  let new_g ← mk_meta_var new_target
  let gs ← get_goals
  set_goals [new_g]
  c
  try <| any_goals reflexivity
  let n ← num_goals
  when (n ≠ 0) (fail "convert tactic failed, there are unsolved goals")
  set_goals gs
  let rhs ← instantiate_mvars rhs
  let new_g ← instantiate_mvars new_g
  return (rhs, new_g)
#align conv.convert conv.convert

unsafe def lhs : conv expr := do
  let (_, lhs, rhs) ← target_lhs_rhs
  return lhs
#align conv.lhs conv.lhs

unsafe def rhs : conv expr := do
  let (_, lhs, rhs) ← target_lhs_rhs
  return rhs
#align conv.rhs conv.rhs

/-- `⊢ lhs = rhs` ~~> `⊢ lhs' = rhs` using `h : lhs = lhs'`. -/
unsafe def update_lhs (new_lhs : expr) (h : expr) : conv Unit := do
  transitivity
  rhs >>= unify new_lhs
  exact h
  let t ← target >>= instantiate_mvars
  change t
#align conv.update_lhs conv.update_lhs

/-- Change `lhs` to something definitionally equal to it. -/
unsafe def change (new_lhs : expr) : conv Unit := do
  let (r, lhs, rhs) ← target_lhs_rhs
  let new_target ← mk_app r [new_lhs, rhs]
  tactic.change new_target
#align conv.change conv.change

/-- Use reflexivity to prove. -/
unsafe def skip : conv Unit :=
  reflexivity
#align conv.skip conv.skip

/-- Put LHS in WHNF. -/
unsafe def whnf : conv Unit :=
  lhs >>= tactic.whnf >>= change
#align conv.whnf conv.whnf

/-- dsimp the LHS. -/
unsafe def dsimp (s : Option simp_lemmas := none) (u : List Name := []) (cfg : DsimpConfig := { }) :
    conv Unit := do
  let s ←
    match s with
      | some s => return s
      | none => simp_lemmas.mk_default
  let l ← lhs
  s u l cfg >>= change
#align conv.dsimp conv.dsimp

private unsafe def congr_aux : List CongrArgKind → List expr → tactic (List expr × List expr)
  | [], [] => return ([], [])
  | k :: ks, a :: as => do
    let (gs, largs) ← congr_aux ks as
    match k with
      |-- parameter for the congruence lemma
        CongrArgKind.fixed =>
        return <| (gs, a :: largs)
      |-- parameter which is a subsingleton
        CongrArgKind.fixed_no_param =>
        return <| (gs, largs)
      | CongrArgKind.eq => do
        let a_type ← infer_type a
        let rhs ← mk_meta_var a_type
        let g_type ← mk_app `eq [a, rhs]
        let g ← mk_meta_var g_type
        -- proof that `a = rhs`
            return
            (g :: gs, a :: rhs :: g :: largs)
      | CongrArgKind.cast => return <| (gs, a :: largs)
      | _ => fail "congr tactic failed, unsupported congruence lemma"
  | ks, as => fail "congr tactic failed, unsupported congruence lemma"
#align conv.congr_aux conv.congr_aux

/--
Take the target equality `f x y = X` and try to apply the congruence lemma for `f` to it (namely `x = x' → y = y' → f x y = f x' y'`). -/
unsafe def congr : conv Unit := do
  let (r, lhs, rhs) ← target_lhs_rhs
  guard (r = `eq)
  let fn := lhs.get_app_fn
  let args := lhs.get_app_args
  let cgr_lemma ← mk_congr_lemma_simp fn (some args.length)
  let g :: gs ← get_goals
  let (new_gs, lemma_args) ← congr_aux cgr_lemma.arg_kinds args
  let g_val := cgr_lemma.proof.mk_app lemma_args
  unify g g_val
  set_goals <| new_gs ++ gs
  return ()
#align conv.congr conv.congr

/-- Create a conversion from the function extensionality tactic.-/
unsafe def funext : conv Unit :=
  iterate' do
    let (r, lhs, rhs) ← target_lhs_rhs
    guard (r = `eq)
    let expr.lam n _ _ _ ← return lhs
    tactic.applyc `funext
    intro n
    return ()
#align conv.funext conv.funext

end Conv

