/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.backward
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.SetGetOptionTactics

namespace Tactic

unsafe axiom back_lemmas : Type
#align tactic.back_lemmas tactic.back_lemmas

/-- Create a datastructure containing all lemmas tagged as [intro].
   Lemmas are indexed using their head-symbol.
   The head-symbol is computed with respect to the given transparency setting. -/
unsafe axiom mk_back_lemmas_core : Transparency → tactic back_lemmas
#align tactic.mk_back_lemmas_core tactic.mk_back_lemmas_core

/-- (back_lemmas_insert_core m lemmas lemma) adds the given lemma to the set back_lemmas.
   It infers the type of the lemma, and uses its head-symbol as an index.
   The head-symbol is computed with respect to the given transparency setting. -/
unsafe axiom back_lemmas_insert_core : Transparency → back_lemmas → expr → tactic back_lemmas
#align tactic.back_lemmas_insert_core tactic.back_lemmas_insert_core

/-- Return the lemmas that have the same head symbol of the given expression -/
unsafe axiom back_lemmas_find : back_lemmas → expr → tactic (List expr)
#align tactic.back_lemmas_find tactic.back_lemmas_find

unsafe def mk_back_lemmas : tactic back_lemmas :=
  mk_back_lemmas_core reducible
#align tactic.mk_back_lemmas tactic.mk_back_lemmas

unsafe def back_lemmas_insert : back_lemmas → expr → tactic back_lemmas :=
  back_lemmas_insert_core reducible
#align tactic.back_lemmas_insert tactic.back_lemmas_insert

/--
(backward_chaining_core t insts max_depth pre_tactic leaf_tactic lemmas): perform backward chaining using
   the lemmas marked as [intro] and extra_lemmas.

   The search maximum depth is \c max_depth.

   Before processing each goal, the tactic pre_tactic is invoked. The possible outcomes are:
      1) it closes the goal
      2) it does nothing, and backward_chaining_core tries applicable lemmas.
      3) it fails, and backward_chaining_core backtracks.

   Whenever no lemma is applicable, the leaf_tactic is invoked, to try to close the goal.
   If insts is tt, then type class resolution is used to discharge goals.

   Remark pre_tactic may also be used to trace the execution of backward_chaining_core -/
unsafe axiom backward_chaining_core :
    Transparency → Bool → Nat → tactic Unit → tactic Unit → back_lemmas → tactic Unit
#align tactic.backward_chaining_core tactic.backward_chaining_core

unsafe def back_lemmas_add_extra : Transparency → back_lemmas → List expr → tactic back_lemmas
  | m, bls, [] => return bls
  | m, bls, l :: ls => do
    let new_bls ← back_lemmas_insert_core m bls l
    back_lemmas_add_extra m new_bls ls
#align tactic.back_lemmas_add_extra tactic.back_lemmas_add_extra

unsafe def back_chaining_core (pre_tactic : tactic Unit) (leaf_tactic : tactic Unit)
    (extra_lemmas : List expr) : tactic Unit := do
  let intro_lemmas ← mk_back_lemmas_core reducible
  let new_lemmas ← back_lemmas_add_extra reducible intro_lemmas extra_lemmas
  let max ← get_nat_option `back_chaining.max_depth 8
  backward_chaining_core reducible tt max pre_tactic leaf_tactic new_lemmas
#align tactic.back_chaining_core tactic.back_chaining_core

unsafe def back_chaining : tactic Unit :=
  back_chaining_core skip assumption []
#align tactic.back_chaining tactic.back_chaining

unsafe def back_chaining_using : List expr → tactic Unit :=
  back_chaining_core skip assumption
#align tactic.back_chaining_using tactic.back_chaining_using

unsafe def back_chaining_using_hs : tactic Unit :=
  local_context >>= back_chaining_core skip failed
#align tactic.back_chaining_using_hs tactic.back_chaining_using_hs

end Tactic

