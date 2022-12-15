/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn

! This file was ported from Lean 3 source module init.data.list.lemmas
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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

/-! append -/


#print List.nil_append /-
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

/-! length -/


#print List.length_cons /-
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

#print List.length_repeat /-
@[simp]
theorem length_repeat (a : α) (n : ℕ) : length (repeat a n) = n := by
  induction n <;> simp [*] <;> rfl
#align list.length_repeat List.length_repeat
-/

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

/-! map -/


/- warning: list.map_cons -> List.map_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (a : α) (l : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.cons.{u1} α a l)) (List.cons.{u2} β (f a) (List.map.{u1, u2} α β f l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (a : α) (l : List.{u2} α), Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β f (List.cons.{u2} α a l)) (List.cons.{u1} β (f a) (List.map.{u2, u1} α β f l))
Case conversion may be inaccurate. Consider using '#align list.map_cons List.map_consₓ'. -/
theorem map_cons (f : α → β) (a l) : map f (a :: l) = f a :: map f l :=
  rfl
#align list.map_cons List.map_cons

/- warning: list.map_append -> List.map_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (List.map.{u1, u2} α β f l₁) (List.map.{u1, u2} α β f l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (l₁ : List.{u2} α) (l₂ : List.{u2} α), Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β f (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l₁ l₂)) (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) (List.map.{u2, u1} α β f l₁) (List.map.{u2, u1} α β f l₂))
Case conversion may be inaccurate. Consider using '#align list.map_append List.map_appendₓ'. -/
@[simp]
theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  intro l₁ <;> induction l₁ <;> intros <;> simp [*]
#align list.map_append List.map_append

/- warning: list.map_singleton -> List.map_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (a : α), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.cons.{u1} α a (List.nil.{u1} α))) (List.cons.{u2} β (f a) (List.nil.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (a : α), Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β f (List.cons.{u2} α a (List.nil.{u2} α))) (List.cons.{u1} β (f a) (List.nil.{u1} β))
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
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (g : β -> γ) (f : α -> β) (l : List.{u1} α), Eq.{succ u3} (List.{u3} γ) (List.map.{u2, u3} β γ g (List.map.{u1, u2} α β f l)) (List.map.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) l)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (g : α -> β) (f : γ -> α) (l : List.{u1} γ), Eq.{succ u2} (List.{u2} β) (List.map.{u3, u2} α β g (List.map.{u1, u3} γ α f l)) (List.map.{u1, u2} γ β (Function.comp.{succ u1, succ u3, succ u2} γ α β g f) l)
Case conversion may be inaccurate. Consider using '#align list.map_map List.map_mapₓ'. -/
@[simp]
theorem map_map (g : β → γ) (f : α → β) (l : List α) : map g (map f l) = map (g ∘ f) l := by
  induction l <;> simp [*]
#align list.map_map List.map_map

/- warning: list.length_map -> List.length_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (l : List.{u1} α), Eq.{1} Nat (List.length.{u2} β (List.map.{u1, u2} α β f l)) (List.length.{u1} α l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : List.{u1} α) (l : α -> β), Eq.{1} Nat (List.length.{u2} β (List.map.{u1, u2} α β l f)) (List.length.{u1} α f)
Case conversion may be inaccurate. Consider using '#align list.length_map List.length_mapₓ'. -/
@[simp]
theorem length_map (f : α → β) (l : List α) : length (map f l) = length l := by
  induction l <;> simp [*]
#align list.length_map List.length_map

/-! bind -/


/- warning: list.nil_bind -> List.nil_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> (List.{u2} β)), Eq.{succ u2} (List.{u2} β) (List.bind.{u1, u2} α β (List.nil.{u1} α) f) (List.nil.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> (List.{u1} β)), Eq.{succ u1} (List.{u1} β) (List.bind.{u2, u1} α β (List.nil.{u2} α) f) (List.nil.{u1} β)
Case conversion may be inaccurate. Consider using '#align list.nil_bind List.nil_bindₓ'. -/
@[simp]
theorem nil_bind (f : α → List β) : List.bind [] f = [] := by simp [join, List.bind]
#align list.nil_bind List.nil_bind

/- warning: list.cons_bind -> List.cons_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (x : α) (xs : List.{u1} α) (f : α -> (List.{u2} β)), Eq.{succ u2} (List.{u2} β) (List.bind.{u1, u2} α β (List.cons.{u1} α x xs) f) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (f x) (List.bind.{u1, u2} α β xs f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (x : α) (xs : List.{u2} α) (f : α -> (List.{u1} β)), Eq.{succ u1} (List.{u1} β) (List.bind.{u2, u1} α β (List.cons.{u2} α x xs) f) (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) (f x) (List.bind.{u2, u1} α β xs f))
Case conversion may be inaccurate. Consider using '#align list.cons_bind List.cons_bindₓ'. -/
@[simp]
theorem cons_bind (x xs) (f : α → List β) : List.bind (x :: xs) f = f x ++ List.bind xs f := by
  simp [join, List.bind]
#align list.cons_bind List.cons_bind

/- warning: list.append_bind -> List.append_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (xs : List.{u1} α) (ys : List.{u1} α) (f : α -> (List.{u2} β)), Eq.{succ u2} (List.{u2} β) (List.bind.{u1, u2} α β (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) xs ys) f) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (List.bind.{u1, u2} α β xs f) (List.bind.{u1, u2} α β ys f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (xs : List.{u2} α) (ys : List.{u2} α) (f : α -> (List.{u1} β)), Eq.{succ u1} (List.{u1} β) (List.bind.{u2, u1} α β (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) xs ys) f) (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) (List.bind.{u2, u1} α β xs f) (List.bind.{u2, u1} α β ys f))
Case conversion may be inaccurate. Consider using '#align list.append_bind List.append_bindₓ'. -/
@[simp]
theorem append_bind (xs ys) (f : α → List β) :
    List.bind (xs ++ ys) f = List.bind xs f ++ List.bind ys f := by
  induction xs <;> [rfl, simp [*, cons_bind]]
#align list.append_bind List.append_bind

/-! mem -/


#print List.mem_nil_iff /-
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
theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s <;> simp [*, or_assoc']
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
    · exact Or.inr ⟨x, h, px⟩, fun o =>
    o.elim (fun pa => ⟨a, mem_cons_self _ _, pa⟩) fun ⟨x, h, px⟩ => ⟨x, mem_cons_of_mem _ h, px⟩⟩
#align list.bex_cons List.bex_cons

theorem ball_cons (p : α → Prop) (a : α) (l : List α) : (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
  ⟨fun al => ⟨al a (mem_cons_self _ _), fun x h => al x (mem_cons_of_mem _ h)⟩, fun ⟨pa, al⟩ x o =>
    o.elim (fun e => e.symm ▸ pa) (al x)⟩
#align list.ball_cons List.ball_cons

/-! list subset -/


#print List.Subset /-
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
theorem Subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ := fun b i =>
  h₂ (h₁ i)
#align list.subset.trans List.Subset.trans
-/

#print List.subset_cons /-
@[simp]
theorem subset_cons (a : α) (l : List α) : l ⊆ a :: l := fun b i => Or.inr i
#align list.subset_cons List.subset_cons
-/

#print List.subset_of_cons_subset /-
theorem subset_of_cons_subset {a : α} {l₁ l₂ : List α} : a :: l₁ ⊆ l₂ → l₁ ⊆ l₂ := fun s b i =>
  s (mem_cons_of_mem _ i)
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

/- warning: list.length_map₂ -> List.length_map₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{1} Nat (List.length.{u3} γ (List.map₂.{u1, u2, u3} α β γ f l₁ l₂)) (LinearOrder.min.{0} Nat Nat.linearOrder (List.length.{u1} α l₁) (List.length.{u2} β l₂))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (l₁ : List.{u3} α) (l₂ : List.{u2} β), Eq.{1} Nat (List.length.{u1} γ (List.map₂.{u3, u2, u1} α β γ f l₁ l₂)) (Min.min.{0} Nat Nat.instMinNat (List.length.{u3} α l₁) (List.length.{u2} β l₂))
Case conversion may be inaccurate. Consider using '#align list.length_map₂ List.length_map₂ₓ'. -/
@[simp]
theorem length_map₂ (f : α → β → γ) (l₁) :
    ∀ l₂, length (map₂ f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ <;> intro l₂ <;> cases l₂ <;>
    simp [*, add_one, min_succ_succ, Nat.zero_min, Nat.min_zero]
#align list.length_map₂ List.length_map₂

/- warning: list.length_take -> List.length_take is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (i : Nat) (l : List.{u1} α), Eq.{1} Nat (List.length.{u1} α (List.take.{u1} α i l)) (LinearOrder.min.{0} Nat Nat.linearOrder i (List.length.{u1} α l))
but is expected to have type
  forall {α : Type.{u1}} (i : Nat) (l : List.{u1} α), Eq.{1} Nat (List.length.{u1} α (List.take.{u1} α i l)) (Min.min.{0} Nat Nat.instMinNat i (List.length.{u1} α l))
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

theorem length_remove_nth :
    ∀ (l : List α) (i : ℕ), i < length l → length (removeNth l i) = length l - 1
  | [], _, h => rfl
  | x :: xs, 0, h => by simp [remove_nth]
  | x :: xs, i + 1, h => by 
    have : i < length xs := lt_of_succ_lt_succ h
    dsimp [remove_nth] <;>
        rw [length_remove_nth xs i this,
          Nat.sub_add_cancel (lt_of_le_of_lt (Nat.zero_le _) this)] <;>
      rfl
#align list.length_remove_nth List.length_remove_nth

/- warning: list.partition_eq_filter_filter -> List.partition_eq_filter_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Eq.{succ u1} (Prod.{u1, u1} (List.{u1} α) (List.{u1} α)) (List.partitionₓ.{u1} α p (fun (a : α) => _inst_1 a) l) (Prod.mk.{u1, u1} (List.{u1} α) (List.{u1} α) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l) (List.filterₓ.{u1} α (Function.comp.{succ u1, 1, 1} α Prop Prop Not p) (fun (a : α) => Not.decidable (p a) (_inst_1 a)) l))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : List.{u1} α), Eq.{succ u1} (Prod.{u1, u1} (List.{u1} α) (List.{u1} α)) (List.partition.{u1} α p _inst_1) (Prod.mk.{u1, u1} (List.{u1} α) (List.{u1} α) (List.filter.{u1} α p _inst_1) (List.filter.{u1} α (Function.comp.{succ u1, 1, 1} α Bool Bool not p) _inst_1))
Case conversion may be inaccurate. Consider using '#align list.partition_eq_filter_filter List.partition_eq_filter_filterₓ'. -/
@[simp]
theorem partition_eq_filter_filter (p : α → Prop) [DecidablePred p] :
    ∀ l : List α, partition p l = (filter p l, filter (Not ∘ p) l)
  | [] => rfl
  | a :: l => by by_cases pa : p a <;> simp [partition, filter, pa, partition_eq_filter_filter l]
#align list.partition_eq_filter_filter List.partition_eq_filter_filter

/-! sublists -/


#print List.Sublist /-
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

/-! filter -/


@[simp]
theorem filter_nil (p : α → Prop) [h : DecidablePred p] : filter p [] = [] :=
  rfl
#align list.filter_nil List.filter_nil

@[simp]
theorem filter_cons_of_pos {p : α → Prop} [h : DecidablePred p] {a : α} :
    ∀ l, p a → filter p (a :: l) = a :: filter p l := fun l pa => if_pos pa
#align list.filter_cons_of_pos List.filter_cons_of_pos

@[simp]
theorem filter_cons_of_neg {p : α → Prop} [h : DecidablePred p] {a : α} :
    ∀ l, ¬p a → filter p (a :: l) = filter p l := fun l pa => if_neg pa
#align list.filter_cons_of_neg List.filter_cons_of_neg

@[simp]
theorem filter_append {p : α → Prop} [h : DecidablePred p] :
    ∀ l₁ l₂ : List α, filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂
  | [], l₂ => rfl
  | a :: l₁, l₂ => by by_cases pa : p a <;> simp [pa, filter_append]
#align list.filter_append List.filter_append

@[simp]
theorem filter_sublist {p : α → Prop} [h : DecidablePred p] : ∀ l : List α, filter p l <+ l
  | [] => Sublist.slnil
  | a :: l =>
    if pa : p a then by simp [pa] <;> apply sublist.cons2 <;> apply filter_sublist l
    else by simp [pa] <;> apply sublist.cons <;> apply filter_sublist l
#align list.filter_sublist List.filter_sublist

/-! map_accumr -/


section MapAccumr

variable {φ : Type w₁} {σ : Type w₂}

/- warning: list.map_accumr -> List.mapAccumr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}}, (α -> σ -> (Prod.{u3, u2} σ β)) -> (List.{u1} α) -> σ -> (Prod.{u3, u2} σ (List.{u2} β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}}, (β -> α -> (Prod.{u1, u3} α σ)) -> (List.{u2} β) -> α -> (Prod.{u1, u3} α (List.{u3} σ))
Case conversion may be inaccurate. Consider using '#align list.map_accumr List.mapAccumrₓ'. -/
-- This runs a function over a list returning the intermediate results and a
-- a final result.
def mapAccumr (f : α → σ → σ × β) : List α → σ → σ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := map_accumr yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)
#align list.map_accumr List.mapAccumr

/- warning: list.length_map_accumr -> List.length_mapAccumr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} (f : α -> σ -> (Prod.{u3, u2} σ β)) (x : List.{u1} α) (s : σ), Eq.{1} Nat (List.length.{u2} β (Prod.snd.{u3, u2} σ (List.{u2} β) (List.mapAccumr.{u1, u2, u3} α β σ f x s))) (List.length.{u1} α x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} (f : β -> α -> (Prod.{u3, u1} α σ)) (x : List.{u2} β) (s : α), Eq.{1} Nat (List.length.{u1} σ (Prod.snd.{u3, u1} α (List.{u1} σ) (List.mapAccumr.{u3, u2, u1} α β σ f x s))) (List.length.{u2} β x)
Case conversion may be inaccurate. Consider using '#align list.length_map_accumr List.length_mapAccumrₓ'. -/
@[simp]
theorem length_mapAccumr :
    ∀ (f : α → σ → σ × β) (x : List α) (s : σ), length (mapAccumr f x s).2 = length x
  | f, a :: x, s => congr_arg succ (length_map_accumr f x s)
  | f, [], s => rfl
#align list.length_map_accumr List.length_mapAccumr

end MapAccumr

section MapAccumr₂

variable {φ : Type w₁} {σ : Type w₂}

/- warning: list.map_accumr₂ -> List.mapAccumr₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Type.{u3}} {σ : Type.{u4}}, (α -> β -> σ -> (Prod.{u4, u3} σ φ)) -> (List.{u1} α) -> (List.{u2} β) -> σ -> (Prod.{u4, u3} σ (List.{u3} φ))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Type.{u3}} {σ : Type.{u4}}, (φ -> σ -> β -> (Prod.{u2, u1} β α)) -> (List.{u3} φ) -> (List.{u4} σ) -> β -> (Prod.{u2, u1} β (List.{u1} α))
Case conversion may be inaccurate. Consider using '#align list.map_accumr₂ List.mapAccumr₂ₓ'. -/
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

/- warning: list.length_map_accumr₂ -> List.length_mapAccumr₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {φ : Type.{u3}} {σ : Type.{u4}} (f : α -> β -> σ -> (Prod.{u4, u3} σ φ)) (x : List.{u1} α) (y : List.{u2} β) (c : σ), Eq.{1} Nat (List.length.{u3} φ (Prod.snd.{u4, u3} σ (List.{u3} φ) (List.mapAccumr₂.{u1, u2, u3, u4} α β φ σ f x y c))) (LinearOrder.min.{0} Nat Nat.linearOrder (List.length.{u1} α x) (List.length.{u2} β y))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {φ : Type.{u2}} {σ : Type.{u1}} (f : φ -> σ -> β -> (Prod.{u4, u3} β α)) (x : List.{u2} φ) (y : List.{u1} σ) (c : β), Eq.{1} Nat (List.length.{u3} α (Prod.snd.{u4, u3} β (List.{u3} α) (List.mapAccumr₂.{u3, u4, u2, u1} α β φ σ f x y c))) (Min.min.{0} Nat Nat.instMinNat (List.length.{u2} φ x) (List.length.{u1} σ y))
Case conversion may be inaccurate. Consider using '#align list.length_map_accumr₂ List.length_mapAccumr₂ₓ'. -/
@[simp]
theorem length_mapAccumr₂ :
    ∀ (f : α → β → σ → σ × φ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
  | f, a :: x, b :: y, c =>
    calc
      succ (length (mapAccumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congr_arg succ (length_map_accumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (min_succ_succ (length x) (length y))
      
  | f, a :: x, [], c => rfl
  | f, [], b :: y, c => rfl
  | f, [], [], c => rfl
#align list.length_map_accumr₂ List.length_mapAccumr₂

end MapAccumr₂

end List

