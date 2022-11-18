/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
prelude
import Leanbin.Init.Data.List.Basic
import Leanbin.Init.Function
import Leanbin.Init.Meta.Default
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Meta.Smt.Rsimp

universe u v w w₁ w₂

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

open Nat

#print List.nil_append /-
-- append
@[simp]
theorem nil_append (s : List α) : [] ++ s = s :=
  rfl
#align list.nil_append List.nil_append
-/

#print List.cons_append /-
@[simp]
theorem cons_append (x : α) (s t : List α) : x :: s ++ t = x :: (s ++ t) :=
  rfl
#align list.cons_append List.cons_append
-/

#print List.append_nil /-
@[simp]
theorem append_nil (t : List α) : t ++ [] = t := by induction t <;> simp [*]
#align list.append_nil List.append_nil
-/

#print List.append_assoc /-
@[simp]
theorem append_assoc (s t u : List α) : s ++ t ++ u = s ++ (t ++ u) := by induction s <;> simp [*]
#align list.append_assoc List.append_assoc
-/

#print List.length_cons /-
-- length
theorem length_cons (a : α) (l : List α) : length (a :: l) = length l + 1 :=
  rfl
#align list.length_cons List.length_cons
-/

#print List.length_append /-
@[simp]
theorem length_append (s t : List α) : length (s ++ t) = length s + length t := by
  induction s
  · show length t = 0 + length t
    · rw [Nat.zero_add]
      
    
  · simp [*, Nat.add_comm, Nat.add_left_comm]
    
#align list.length_append List.length_append
-/

@[simp]
theorem length_repeat (a : α) (n : ℕ) : length (repeat a n) = n := by induction n <;> simp [*] <;> rfl
#align list.length_repeat List.length_repeat

#print List.length_tail /-
@[simp]
theorem length_tail (l : List α) : length (tail l) = length l - 1 := by cases l <;> rfl
#align list.length_tail List.length_tail
-/

#print List.length_drop /-
-- TODO(Leo): cleanup proof after arith dec proc
@[simp]
theorem length_drop : ∀ (i : ℕ) (l : List α), length (drop i l) = length l - i
  | 0, l => rfl
  | succ i, [] => Eq.symm (Nat.zero_sub (succ i))
  | succ i, x :: l =>
    calc
      length (drop (succ i) (x :: l)) = length l - i := length_drop i l
      _ = succ (length l) - succ i := (Nat.succ_sub_succ_eq_sub (length l) i).symm
      
#align list.length_drop List.length_drop
-/

/- warning: list.map_cons -> List.map_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} (f : α -> β) (a : α) (l : List.{u} α), Eq.{succ v} (List.{v} β) (List.map.{u v} α β f (List.cons.{u} α a l)) (List.cons.{v} β (f a) (List.map.{u v} α β f l))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (a : α) (l : List.{u_1} α), Eq.{succ u_2} (List.{u_2} β) (List.map.{u_1 u_2} α β f (List.cons.{u_1} α a l)) (List.cons.{u_2} β (f a) (List.map.{u_1 u_2} α β f l))
Case conversion may be inaccurate. Consider using '#align list.map_cons List.map_consₓ'. -/
-- map
theorem map_cons (f : α → β) (a l) : map f (a :: l) = f a :: map f l :=
  rfl
#align list.map_cons List.map_cons

/- warning: list.map_append -> List.map_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} (f : α -> β) (l₁ : List.{u} α) (l₂ : List.{u} α), Eq.{succ v} (List.{v} β) (List.map.{u v} α β f (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) l₁ l₂)) (Append.append.{v} (List.{v} β) (List.hasAppend.{v} β) (List.map.{u v} α β f l₁) (List.map.{u v} α β f l₂))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (l₁ : List.{u_1} α) (l₂ : List.{u_1} α), Eq.{succ u_2} (List.{u_2} β) (List.map.{u_1 u_2} α β f (HAppend.hAppend.{u_1 u_1 u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α) (instHAppend.{u_1} (List.{u_1} α) (List.instAppendList.{u_1} α)) l₁ l₂)) (HAppend.hAppend.{u_2 u_2 u_2} (List.{u_2} β) (List.{u_2} β) (List.{u_2} β) (instHAppend.{u_2} (List.{u_2} β) (List.instAppendList.{u_2} β)) (List.map.{u_1 u_2} α β f l₁) (List.map.{u_1 u_2} α β f l₂))
Case conversion may be inaccurate. Consider using '#align list.map_append List.map_appendₓ'. -/
@[simp]
theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  intro l₁ <;> induction l₁ <;> intros <;> simp [*]
#align list.map_append List.map_append

/- warning: list.map_singleton -> List.map_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} (f : α -> β) (a : α), Eq.{succ v} (List.{v} β) (List.map.{u v} α β f (List.cons.{u} α a (List.nil.{u} α))) (List.cons.{v} β (f a) (List.nil.{v} β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (a : α), Eq.{succ u_2} (List.{u_2} β) (List.map.{u_1 u_2} α β f (List.cons.{u_1} α a (List.nil.{u_1} α))) (List.cons.{u_2} β (f a) (List.nil.{u_2} β))
Case conversion may be inaccurate. Consider using '#align list.map_singleton List.map_singletonₓ'. -/
theorem map_singleton (f : α → β) (a : α) : map f [a] = [f a] :=
  rfl
#align list.map_singleton List.map_singleton

#print List.map_id /-
@[simp]
theorem map_id (l : List α) : map id l = l := by induction l <;> simp [*]
#align list.map_id List.map_id
-/

/- warning: list.map_map -> List.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {γ : Type.{w}} (g : β -> γ) (f : α -> β) (l : List.{u} α), Eq.{succ w} (List.{w} γ) (List.map.{v w} β γ g (List.map.{u v} α β f l)) (List.map.{u w} α γ (Function.comp.{succ u succ v succ w} α β γ g f) l)
but is expected to have type
  forall {β : Type.{u_1}} {γ : Type.{u_2}} {α : Type.{u_3}} (g : β -> γ) (f : α -> β) (l : List.{u_3} α), Eq.{succ u_2} (List.{u_2} γ) (List.map.{u_1 u_2} β γ g (List.map.{u_3 u_1} α β f l)) (List.map.{u_3 u_2} α γ (Function.comp.{succ u_3 succ u_1 succ u_2} α β γ g f) l)
Case conversion may be inaccurate. Consider using '#align list.map_map List.map_mapₓ'. -/
@[simp]
theorem map_map (g : β → γ) (f : α → β) (l : List α) : map g (map f l) = map (g ∘ f) l := by induction l <;> simp [*]
#align list.map_map List.map_map

/- warning: list.length_map -> List.length_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} (f : α -> β) (l : List.{u} α), Eq.{1} Nat (List.length.{v} β (List.map.{u v} α β f l)) (List.length.{u} α l)
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} (as : List.{u} α) (f : α -> β), Eq.{1} Nat (List.length.{v} β (List.map.{u v} α β f as)) (List.length.{u} α as)
Case conversion may be inaccurate. Consider using '#align list.length_map List.length_mapₓ'. -/
@[simp]
theorem length_map (f : α → β) (l : List α) : length (map f l) = length l := by induction l <;> simp [*]
#align list.length_map List.length_map

/- warning: list.nil_bind -> List.nil_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} (f : α -> (List.{v} β)), Eq.{succ v} (List.{v} β) (List.bind.{u v} α β (List.nil.{u} α) f) (List.nil.{v} β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> (List.{u_2} β)), Eq.{succ u_2} (List.{u_2} β) (List.bind.{u_1 u_2} α β (List.nil.{u_1} α) f) (List.nil.{u_2} β)
Case conversion may be inaccurate. Consider using '#align list.nil_bind List.nil_bindₓ'. -/
-- bind
@[simp]
theorem nil_bind (f : α → List β) : List.bind [] f = [] := by simp [join, List.bind]
#align list.nil_bind List.nil_bind

/- warning: list.cons_bind -> List.cons_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} (x : α) (xs : List.{u} α) (f : α -> (List.{v} β)), Eq.{succ v} (List.{v} β) (List.bind.{u v} α β (List.cons.{u} α x xs) f) (Append.append.{v} (List.{v} β) (List.hasAppend.{v} β) (f x) (List.bind.{u v} α β xs f))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : α) (xs : List.{u_1} α) (f : α -> (List.{u_2} β)), Eq.{succ u_2} (List.{u_2} β) (List.bind.{u_1 u_2} α β (List.cons.{u_1} α x xs) f) (HAppend.hAppend.{u_2 u_2 u_2} (List.{u_2} β) (List.{u_2} β) (List.{u_2} β) (instHAppend.{u_2} (List.{u_2} β) (List.instAppendList.{u_2} β)) (f x) (List.bind.{u_1 u_2} α β xs f))
Case conversion may be inaccurate. Consider using '#align list.cons_bind List.cons_bindₓ'. -/
@[simp]
theorem cons_bind (x xs) (f : α → List β) : List.bind (x :: xs) f = f x ++ List.bind xs f := by simp [join, List.bind]
#align list.cons_bind List.cons_bind

/- warning: list.append_bind -> List.append_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} (xs : List.{u} α) (ys : List.{u} α) (f : α -> (List.{v} β)), Eq.{succ v} (List.{v} β) (List.bind.{u v} α β (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) xs ys) f) (Append.append.{v} (List.{v} β) (List.hasAppend.{v} β) (List.bind.{u v} α β xs f) (List.bind.{u v} α β ys f))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (xs : List.{u_1} α) (ys : List.{u_1} α) (f : α -> (List.{u_2} β)), Eq.{succ u_2} (List.{u_2} β) (List.bind.{u_1 u_2} α β (HAppend.hAppend.{u_1 u_1 u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α) (instHAppend.{u_1} (List.{u_1} α) (List.instAppendList.{u_1} α)) xs ys) f) (HAppend.hAppend.{u_2 u_2 u_2} (List.{u_2} β) (List.{u_2} β) (List.{u_2} β) (instHAppend.{u_2} (List.{u_2} β) (List.instAppendList.{u_2} β)) (List.bind.{u_1 u_2} α β xs f) (List.bind.{u_1 u_2} α β ys f))
Case conversion may be inaccurate. Consider using '#align list.append_bind List.append_bindₓ'. -/
@[simp]
theorem append_bind (xs ys) (f : α → List β) : List.bind (xs ++ ys) f = List.bind xs f ++ List.bind ys f := by
  induction xs <;> [rfl, simp [*, cons_bind]]
#align list.append_bind List.append_bind

#print List.mem_nil_iff /-
-- mem
theorem mem_nil_iff (a : α) : a ∈ ([] : List α) ↔ False :=
  Iff.rfl
#align list.mem_nil_iff List.mem_nil_iff
-/

#print List.not_mem_nil /-
@[simp]
theorem not_mem_nil (a : α) : a ∉ ([] : List α) :=
  not_false
#align list.not_mem_nil List.not_mem_nil
-/

#print List.mem_cons_self /-
theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l :=
  Or.inl rfl
#align list.mem_cons_self List.mem_cons_self
-/

@[simp]
theorem mem_cons_iff (a y : α) (l : List α) : a ∈ y :: l ↔ a = y ∨ a ∈ l :=
  Iff.rfl
#align list.mem_cons_iff List.mem_cons_iff

@[rsimp]
theorem mem_cons_eq (a y : α) (l : List α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
  rfl
#align list.mem_cons_eq List.mem_cons_eq

#print List.mem_cons_of_mem /-
theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l := fun H => Or.inr H
#align list.mem_cons_of_mem List.mem_cons_of_mem
-/

#print List.eq_or_mem_of_mem_cons /-
theorem eq_or_mem_of_mem_cons {a y : α} {l : List α} : a ∈ y :: l → a = y ∨ a ∈ l := fun h => h
#align list.eq_or_mem_of_mem_cons List.eq_or_mem_of_mem_cons
-/

#print List.mem_append /-
@[simp]
theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by induction s <;> simp [*, or_assoc']
#align list.mem_append List.mem_append
-/

#print List.mem_append_eq /-
@[rsimp]
theorem mem_append_eq (a : α) (s t : List α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
  propext mem_append
#align list.mem_append_eq List.mem_append_eq
-/

#print List.mem_append_left /-
theorem mem_append_left {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inl h)
#align list.mem_append_left List.mem_append_left
-/

#print List.mem_append_right /-
theorem mem_append_right {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inr h)
#align list.mem_append_right List.mem_append_right
-/

theorem not_bex_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x := fun ⟨x, hx, px⟩ => hx
#align list.not_bex_nil List.not_bex_nil

theorem ball_nil (p : α → Prop) : ∀ x ∈ @nil α, p x := fun x => False.elim
#align list.ball_nil List.ball_nil

theorem bex_cons (p : α → Prop) (a : α) (l : List α) : (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  ⟨fun ⟨x, h, px⟩ => by
    simp at h
    cases' h with h h
    · cases h
      exact Or.inl px
      
    · exact Or.inr ⟨x, h, px⟩
      ,
    fun o => o.elim (fun pa => ⟨a, mem_cons_self _ _, pa⟩) fun ⟨x, h, px⟩ => ⟨x, mem_cons_of_mem _ h, px⟩⟩
#align list.bex_cons List.bex_cons

theorem ball_cons (p : α → Prop) (a : α) (l : List α) : (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
  ⟨fun al => ⟨al a (mem_cons_self _ _), fun x h => al x (mem_cons_of_mem _ h)⟩, fun ⟨pa, al⟩ x o =>
    o.elim (fun e => e.symm ▸ pa) (al x)⟩
#align list.ball_cons List.ball_cons

#print List.Subset /-
-- list subset
protected def Subset (l₁ l₂ : List α) :=
  ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂
#align list.subset List.Subset
-/

instance : HasSubset (List α) :=
  ⟨List.Subset⟩

#print List.nil_subset /-
@[simp]
theorem nil_subset (l : List α) : [] ⊆ l := fun b i => False.elim (Iff.mp (mem_nil_iff b) i)
#align list.nil_subset List.nil_subset
-/

#print List.Subset.refl /-
@[refl, simp]
theorem Subset.refl (l : List α) : l ⊆ l := fun b i => i
#align list.subset.refl List.Subset.refl
-/

#print List.Subset.trans /-
@[trans]
theorem Subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ := fun b i => h₂ (h₁ i)
#align list.subset.trans List.Subset.trans
-/

#print List.subset_cons /-
@[simp]
theorem subset_cons (a : α) (l : List α) : l ⊆ a :: l := fun b i => Or.inr i
#align list.subset_cons List.subset_cons
-/

#print List.subset_of_cons_subset /-
theorem subset_of_cons_subset {a : α} {l₁ l₂ : List α} : a :: l₁ ⊆ l₂ → l₁ ⊆ l₂ := fun s b i => s (mem_cons_of_mem _ i)
#align list.subset_of_cons_subset List.subset_of_cons_subset
-/

#print List.cons_subset_cons /-
theorem cons_subset_cons {l₁ l₂ : List α} (a : α) (s : l₁ ⊆ l₂) : a :: l₁ ⊆ a :: l₂ := fun b hin =>
  Or.elim (eq_or_mem_of_mem_cons hin) (fun e : b = a => Or.inl e) fun i : b ∈ l₁ => Or.inr (s i)
#align list.cons_subset_cons List.cons_subset_cons
-/

#print List.subset_append_left /-
@[simp]
theorem subset_append_left (l₁ l₂ : List α) : l₁ ⊆ l₁ ++ l₂ := fun b => mem_append_left _
#align list.subset_append_left List.subset_append_left
-/

#print List.subset_append_right /-
@[simp]
theorem subset_append_right (l₁ l₂ : List α) : l₂ ⊆ l₁ ++ l₂ := fun b => mem_append_right _
#align list.subset_append_right List.subset_append_right
-/

#print List.subset_cons_of_subset /-
theorem subset_cons_of_subset (a : α) {l₁ l₂ : List α} : l₁ ⊆ l₂ → l₁ ⊆ a :: l₂ :=
  fun (s : l₁ ⊆ l₂) (a : α) (i : a ∈ l₁) => Or.inr (s i)
#align list.subset_cons_of_subset List.subset_cons_of_subset
-/

#print List.eq_nil_of_length_eq_zero /-
theorem eq_nil_of_length_eq_zero {l : List α} : length l = 0 → l = [] := by
  induction l <;> intros
  rfl
  contradiction
#align list.eq_nil_of_length_eq_zero List.eq_nil_of_length_eq_zero
-/

#print List.ne_nil_of_length_eq_succ /-
theorem ne_nil_of_length_eq_succ {l : List α} : ∀ {n : Nat}, length l = succ n → l ≠ [] := by
  induction l <;> intros <;> contradiction
#align list.ne_nil_of_length_eq_succ List.ne_nil_of_length_eq_succ
-/

@[simp]
theorem length_map₂ (f : α → β → γ) (l₁) : ∀ l₂, length (map₂ f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ <;> intro l₂ <;> cases l₂ <;> simp [*, add_one, min_succ_succ, Nat.zero_min, Nat.min_zero]
#align list.length_map₂ List.length_map₂

/- warning: list.length_take -> List.length_take is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (i : Nat) (l : List.{u} α), Eq.{1} Nat (List.length.{u} α (List.take.{u} α i l)) (LinearOrder.min.{0} Nat Nat.linearOrder i (List.length.{u} α l))
but is expected to have type
  forall {α : Type.{u_1}} (i : Nat) (l : List.{u_1} α), Eq.{1} Nat (List.length.{u_1} α (List.take.{u_1} α i l)) (Min.min.{0} Nat Nat.instMinNat i (List.length.{u_1} α l))
Case conversion may be inaccurate. Consider using '#align list.length_take List.length_takeₓ'. -/
@[simp]
theorem length_take : ∀ (i : ℕ) (l : List α), length (take i l) = min i (length l)
  | 0, l => by simp [Nat.zero_min]
  | succ n, [] => by simp [Nat.min_zero]
  | succ n, a :: l => by simp [*, Nat.min_succ_succ, add_one]
#align list.length_take List.length_take

#print List.length_take_le /-
theorem length_take_le (n) (l : List α) : length (take n l) ≤ n := by simp [min_le_left]
#align list.length_take_le List.length_take_le
-/

theorem length_remove_nth : ∀ (l : List α) (i : ℕ), i < length l → length (removeNth l i) = length l - 1
  | [], _, h => rfl
  | x :: xs, 0, h => by simp [remove_nth]
  | x :: xs, i + 1, h => by
    have : i < length xs := lt_of_succ_lt_succ h
    dsimp [remove_nth] <;>
      rw [length_remove_nth xs i this, Nat.sub_add_cancel (lt_of_le_of_lt (Nat.zero_le _) this)] <;> rfl
#align list.length_remove_nth List.length_remove_nth

/- warning: list.partition_eq_filter_filter -> List.partition_eq_filter_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u} α p] (l : List.{u} α), Eq.{succ u} (Prod.{u u} (List.{u} α) (List.{u} α)) (List.partition'.{u} α p (fun (a : α) => _inst_1 a) l) (Prod.mk.{u u} (List.{u} α) (List.{u} α) (List.filter'.{u} α p (fun (a : α) => _inst_1 a) l) (List.filter'.{u} α (Function.comp.{succ u 1 1} α Prop Prop Not p) (fun (a : α) => Not.decidable (p a) (_inst_1 a)) l))
but is expected to have type
  forall {α : Type.{u_1}} (p : α -> Bool) (l : List.{u_1} α), Eq.{succ u_1} (Prod.{u_1 u_1} (List.{u_1} α) (List.{u_1} α)) (List.partition.{u_1} α p l) (Prod.mk.{u_1 u_1} (List.{u_1} α) (List.{u_1} α) (List.filter.{u_1} α p l) (List.filter.{u_1} α (Function.comp.{succ u_1 1 1} α Bool Bool not p) l))
Case conversion may be inaccurate. Consider using '#align list.partition_eq_filter_filter List.partition_eq_filter_filterₓ'. -/
@[simp]
theorem partition_eq_filter_filter (p : α → Prop) [DecidablePred p] :
    ∀ l : List α, partition' p l = (filter' p l, filter' (Not ∘ p) l)
  | [] => rfl
  | a :: l => by by_cases pa : p a <;> simp [partition, filter, pa, partition_eq_filter_filter l]
#align list.partition_eq_filter_filter List.partition_eq_filter_filter

#print List.Sublist /-
-- sublists
inductive Sublist : List α → List α → Prop
  | slnil : sublist [] []
  | cons (l₁ l₂ a) : sublist l₁ l₂ → sublist l₁ (a :: l₂)
  | cons2 (l₁ l₂ a) : sublist l₁ l₂ → sublist (a :: l₁) (a :: l₂)
#align list.sublist List.Sublist
-/

-- mathport name: «expr <+ »
infixl:50 " <+ " => Sublist

theorem length_le_of_sublist : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → length l₁ ≤ length l₂
  | _, _, sublist.slnil => le_refl 0
  | _, _, sublist.cons l₁ l₂ a s => le_succ_of_le (length_le_of_sublist s)
  | _, _, sublist.cons2 l₁ l₂ a s => succ_le_succ (length_le_of_sublist s)
#align list.length_le_of_sublist List.length_le_of_sublist

-- filter
@[simp]
theorem filter_nil (p : α → Prop) [h : DecidablePred p] : filter' p [] = [] :=
  rfl
#align list.filter_nil List.filter_nil

@[simp]
theorem filter_cons_of_pos {p : α → Prop} [h : DecidablePred p] {a : α} :
    ∀ l, p a → filter' p (a :: l) = a :: filter' p l := fun l pa => if_pos pa
#align list.filter_cons_of_pos List.filter_cons_of_pos

@[simp]
theorem filter_cons_of_neg {p : α → Prop} [h : DecidablePred p] {a : α} :
    ∀ l, ¬p a → filter' p (a :: l) = filter' p l := fun l pa => if_neg pa
#align list.filter_cons_of_neg List.filter_cons_of_neg

@[simp]
theorem filter_append {p : α → Prop} [h : DecidablePred p] :
    ∀ l₁ l₂ : List α, filter' p (l₁ ++ l₂) = filter' p l₁ ++ filter' p l₂
  | [], l₂ => rfl
  | a :: l₁, l₂ => by by_cases pa : p a <;> simp [pa, filter_append]
#align list.filter_append List.filter_append

@[simp]
theorem filter_sublist {p : α → Prop} [h : DecidablePred p] : ∀ l : List α, filter' p l <+ l
  | [] => Sublist.slnil
  | a :: l =>
    if pa : p a then by simp [pa] <;> apply sublist.cons2 <;> apply filter_sublist l
    else by simp [pa] <;> apply sublist.cons <;> apply filter_sublist l
#align list.filter_sublist List.filter_sublist

-- map_accumr
section MapAccumr

variable {φ : Type w₁} {σ : Type w₂}

-- This runs a function over a list returning the intermediate results and a
-- a final result.
def mapAccumr (f : α → σ → σ × β) : List α → σ → σ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := map_accumr yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)
#align list.map_accumr List.mapAccumr

@[simp]
theorem length_map_accumr : ∀ (f : α → σ → σ × β) (x : List α) (s : σ), length (mapAccumr f x s).2 = length x
  | f, a :: x, s => congr_arg succ (length_map_accumr f x s)
  | f, [], s => rfl
#align list.length_map_accumr List.length_map_accumr

end MapAccumr

section MapAccumr₂

variable {φ : Type w₁} {σ : Type w₂}

-- This runs a function over two lists returning the intermediate results and a
-- a final result.
def mapAccumr₂ (f : α → β → σ → σ × φ) : List α → List β → σ → σ × List φ
  | [], _, c => (c, [])
  | _, [], c => (c, [])
  | x :: xr, y :: yr, c =>
    let r := map_accumr₂ xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)
#align list.map_accumr₂ List.mapAccumr₂

@[simp]
theorem length_map_accumr₂ :
    ∀ (f : α → β → σ → σ × φ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
  | f, a :: x, b :: y, c =>
    calc
      succ (length (mapAccumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congr_arg succ (length_map_accumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (min_succ_succ (length x) (length y))
      
  | f, a :: x, [], c => rfl
  | f, [], b :: y, c => rfl
  | f, [], [], c => rfl
#align list.length_map_accumr₂ List.length_map_accumr₂

end MapAccumr₂

end List

