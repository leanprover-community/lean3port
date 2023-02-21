/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.list.instances
! leanprover-community/mathlib commit 9af482290ef68e8aaa5ead01aa7b09b7be7019fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.List.Lemmas

open List

universe u v

attribute [local simp] join List.ret

instance : Monad List where
  pure := @List.ret
  map := @List.map
  bind := @List.bind

instance : LawfulMonad List
    where
  bind_pure_comp_eq_map := by
    intro α β f l
    induction l <;> simp_all [(· <$> ·), (· >>= ·), pure]
  id_map := @List.map_id
  pure_bind := by
    intros
    simp [pure, (· >>= ·)]
  bind_assoc := by
    intro α β γ l f g
    induction' l with x l ih
    · simp [(· >>= ·)]
    · simp [(· >>= ·)] at ih
      simp [(· >>= ·), ih]

instance : Alternative List :=
  { List.monad with
    failure := @List.nil
    orelse := @List.append }

namespace List

variable {α β : Type u} (p : α → Prop) [DecidablePred p]

instance binTreeToList : Coe (BinTree α) (List α) :=
  ⟨BinTree.toList⟩
#align list.bin_tree_to_list List.binTreeToList

/- warning: list.decidable_bex -> List.decidableBex is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Decidable (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) (fun (H : Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) => p x)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Decidable (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) (p x)))
Case conversion may be inaccurate. Consider using '#align list.decidable_bex List.decidableBexₓ'. -/
instance decidableBex : ∀ l : List α, Decidable (∃ x ∈ l, p x)
  | [] => isFalse (by simp [List.not_bex_nil])
  | x :: xs =>
    if h₁ : p x then isTrue ⟨x, mem_cons_self _ _, h₁⟩
    else
      match decidable_bex xs with
      | is_true h₂ =>
        isTrue
          (by
            cases' h₂ with y h; cases' h with hm hp
            exact ⟨y, mem_cons_of_mem _ hm, hp⟩)
      | is_false h₂ =>
        isFalse
          (by
            intro h; cases' h with y h; cases' h with hm hp
            cases eq_or_mem_of_mem_cons hm
            · rw [h] at hp
              contradiction
            · refine' absurd _ h₂
              exact ⟨y, h, hp⟩)
#align list.decidable_bex List.decidableBex

#print List.decidableBall /-
instance decidableBall (l : List α) : Decidable (∀ x ∈ l, p x) :=
  if h : ∃ x ∈ l, ¬p x then
    isFalse <|
      let ⟨x, h, np⟩ := h
      fun al => np (al x h)
  else isTrue fun x hx => if h' : p x then h' else False.elim <| h ⟨x, hx, h'⟩
#align list.decidable_ball List.decidableBall
-/

end List

