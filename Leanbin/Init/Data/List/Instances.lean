/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.List.Lemmas

#align_import init.data.list.instances from "leanprover-community/lean"@"9af482290ef68e8aaa5ead01aa7b09b7be7019fd"

open List

universe u v

attribute [local simp] join List.ret

instance : Monad List where
  pure := @List.ret
  map := @List.map
  bind := @List.bind

instance : LawfulMonad List
    where
  bind_pure_comp := by intro α β f l; induction l <;> simp_all [(· <$> ·), (· >>= ·), pure]
  id_map := @List.map_id
  pure_bind := by intros; simp [pure, (· >>= ·)]
  bind_assoc := by
    intro α β γ l f g; induction' l with x l ih; · simp [(· >>= ·)]
    · simp [(· >>= ·)] at ih ; simp [(· >>= ·), ih]

instance : Alternative List :=
  { List.instMonad with
    failure := @List.nil
    orelse := @List.append }

namespace List

variable {α β : Type u} (p : α → Prop) [DecidablePred p]

instance binTreeToList : Coe (BinTree α) (List α) :=
  ⟨BinTree.toList⟩
#align list.bin_tree_to_list List.binTreeToList

#print List.decidableBex /-
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
            · rw [h] at hp ; contradiction
            · refine' absurd _ h₂
              exact ⟨y, h, hp⟩)
#align list.decidable_bex List.decidableBex
-/

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

