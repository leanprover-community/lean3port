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

-- append
@[simp]
theorem nil_append (s : List α) : [] ++ s = s :=
  rfl

@[simp]
theorem cons_append (x : α) (s t : List α) : x :: s ++ t = x :: (s ++ t) :=
  rfl

@[simp]
theorem append_nil (t : List α) : t ++ [] = t := by
  induction t <;> simp [*]

@[simp]
theorem append_assoc (s t u : List α) : s ++ t ++ u = s ++ (t ++ u) := by
  induction s <;> simp [*]

-- length
theorem length_cons (a : α) (l : List α) : length (a :: l) = length l + 1 :=
  rfl

@[simp]
theorem length_append (s t : List α) : length (s ++ t) = length s + length t := by
  induction s
  · show length t = 0 + length t
    · rw [Nat.zero_add]
      
    
  · simp [*, Nat.add_comm, Nat.add_left_comm]
    

@[simp]
theorem length_repeat (a : α) (n : ℕ) : length (repeat a n) = n := by
  induction n <;> simp [*] <;> rfl

@[simp]
theorem length_tail (l : List α) : length (tail l) = length l - 1 := by
  cases l <;> rfl

-- TODO(Leo): cleanup proof after arith dec proc
@[simp]
theorem length_dropₓ : ∀ (i : ℕ) (l : List α), length (dropₓ i l) = length l - i
  | 0, l => rfl
  | succ i, [] => Eq.symm (Nat.zero_sub (succ i))
  | succ i, x :: l =>
    calc
      length (dropₓ (succ i) (x :: l)) = length l - i := length_drop i l
      _ = succ (length l) - succ i := (Nat.succ_sub_succ_eq_sub (length l) i).symm
      

-- map
theorem map_cons (f : α → β) (a l) : map f (a :: l) = f a :: map f l :=
  rfl

@[simp]
theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  intro l₁ <;> induction l₁ <;> intros <;> simp [*]

theorem map_singleton (f : α → β) (a : α) : map f [a] = [f a] :=
  rfl

@[simp]
theorem map_id (l : List α) : map id l = l := by
  induction l <;> simp [*]

@[simp]
theorem map_mapₓ (g : β → γ) (f : α → β) (l : List α) : map g (map f l) = map (g ∘ f) l := by
  induction l <;> simp [*]

@[simp]
theorem length_mapₓ (f : α → β) (l : List α) : length (map f l) = length l := by
  induction l <;> simp [*]

-- bind
@[simp]
theorem nil_bind (f : α → List β) : List.bind [] f = [] := by
  simp [join, List.bind]

@[simp]
theorem cons_bind (x xs) (f : α → List β) : List.bind (x :: xs) f = f x ++ List.bind xs f := by
  simp [join, List.bind]

@[simp]
theorem append_bind (xs ys) (f : α → List β) : List.bind (xs ++ ys) f = List.bind xs f ++ List.bind ys f := by
  induction xs <;> [rfl, simp [*, cons_bind]]

-- mem
theorem mem_nil_iffₓ (a : α) : a ∈ ([] : List α) ↔ False :=
  Iff.rfl

@[simp]
theorem not_mem_nilₓ (a : α) : a ∉ ([] : List α) :=
  not_false

theorem mem_cons_selfₓ (a : α) (l : List α) : a ∈ a :: l :=
  Or.inl rfl

@[simp]
theorem mem_cons_iffₓ (a y : α) (l : List α) : a ∈ y :: l ↔ a = y ∨ a ∈ l :=
  Iff.rfl

@[rsimp]
theorem mem_cons_eqₓ (a y : α) (l : List α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
  rfl

theorem mem_cons_of_memₓ (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l := fun H => Or.inr H

theorem eq_or_mem_of_mem_consₓ {a y : α} {l : List α} : a ∈ y :: l → a = y ∨ a ∈ l := fun h => h

@[simp]
theorem mem_appendₓ {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s <;> simp [*, or_assoc]

@[rsimp]
theorem mem_append_eqₓ (a : α) (s t : List α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
  propext mem_appendₓ

theorem mem_append_leftₓ {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  mem_appendₓ.2 (Or.inl h)

theorem mem_append_rightₓ {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  mem_appendₓ.2 (Or.inr h)

theorem not_bex_nilₓ (p : α → Prop) : ¬∃ x ∈ @nil α, p x := fun ⟨x, hx, px⟩ => hx

theorem ball_nilₓ (p : α → Prop) : ∀ x ∈ @nil α, p x := fun x => False.elim

theorem bex_consₓ (p : α → Prop) (a : α) (l : List α) : (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  ⟨fun ⟨x, h, px⟩ => by
    simp at h
    cases' h with h h
    · cases h
      exact Or.inl px
      
    · exact Or.inr ⟨x, h, px⟩
      ,
    fun o => o.elim (fun pa => ⟨a, mem_cons_selfₓ _ _, pa⟩) fun ⟨x, h, px⟩ => ⟨x, mem_cons_of_memₓ _ h, px⟩⟩

theorem ball_consₓ (p : α → Prop) (a : α) (l : List α) : (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
  ⟨fun al => ⟨al a (mem_cons_selfₓ _ _), fun x h => al x (mem_cons_of_memₓ _ h)⟩, fun ⟨pa, al⟩ x o =>
    o.elim (fun e => e.symm ▸ pa) (al x)⟩

-- list subset
protected def Subset (l₁ l₂ : List α) :=
  ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂

instance : Subset (List α) :=
  ⟨List.Subset⟩

@[simp]
theorem nil_subsetₓ (l : List α) : [] ⊆ l := fun b i => False.elim (Iff.mp (mem_nil_iffₓ b) i)

@[refl, simp]
theorem Subset.refl (l : List α) : l ⊆ l := fun b i => i

@[trans]
theorem Subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ := fun b i => h₂ (h₁ i)

@[simp]
theorem subset_consₓ (a : α) (l : List α) : l ⊆ a :: l := fun b i => Or.inr i

theorem subset_of_cons_subsetₓ {a : α} {l₁ l₂ : List α} : a :: l₁ ⊆ l₂ → l₁ ⊆ l₂ := fun s b i =>
  s (mem_cons_of_memₓ _ i)

theorem cons_subset_consₓ {l₁ l₂ : List α} (a : α) (s : l₁ ⊆ l₂) : a :: l₁ ⊆ a :: l₂ := fun b hin =>
  Or.elim (eq_or_mem_of_mem_consₓ hin) (fun e : b = a => Or.inl e) fun i : b ∈ l₁ => Or.inr (s i)

@[simp]
theorem subset_append_leftₓ (l₁ l₂ : List α) : l₁ ⊆ l₁ ++ l₂ := fun b => mem_append_leftₓ _

@[simp]
theorem subset_append_rightₓ (l₁ l₂ : List α) : l₂ ⊆ l₁ ++ l₂ := fun b => mem_append_rightₓ _

theorem subset_cons_of_subsetₓ (a : α) {l₁ l₂ : List α} : l₁ ⊆ l₂ → l₁ ⊆ a :: l₂ :=
  fun (s : l₁ ⊆ l₂) (a : α) (i : a ∈ l₁) => Or.inr (s i)

theorem eq_nil_of_length_eq_zero {l : List α} : length l = 0 → l = [] := by
  induction l <;> intros
  rfl
  contradiction

theorem ne_nil_of_length_eq_succ {l : List α} : ∀ {n : Nat}, length l = succ n → l ≠ [] := by
  induction l <;> intros <;> contradiction

@[simp]
theorem length_map₂ₓ (f : α → β → γ) (l₁) : ∀ l₂, length (map₂ₓ f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ <;> intro l₂ <;> cases l₂ <;> simp [*, add_one, min_succ_succ, Nat.zero_minₓ, Nat.min_zeroₓ]

@[simp]
theorem length_takeₓ : ∀ (i : ℕ) (l : List α), length (takeₓ i l) = min i (length l)
  | 0, l => by
    simp [Nat.zero_minₓ]
  | succ n, [] => by
    simp [Nat.min_zeroₓ]
  | succ n, a :: l => by
    simp [*, Nat.min_succ_succₓ, add_one]

theorem length_take_leₓ (n) (l : List α) : length (takeₓ n l) ≤ n := by
  simp [min_le_leftₓ]

theorem length_remove_nth : ∀ (l : List α) (i : ℕ), i < length l → length (removeNthₓ l i) = length l - 1
  | [], _, h => rfl
  | x :: xs, 0, h => by
    simp [remove_nth]
  | x :: xs, i + 1, h => by
    have : i < length xs := lt_of_succ_lt_succₓ h
    dsimp' [remove_nth] <;>
      rw [length_remove_nth xs i this, Nat.sub_add_cancelₓ (lt_of_le_of_ltₓ (Nat.zero_leₓ _) this)] <;> rfl

@[simp]
theorem partition_eq_filter_filter (p : α → Prop) [DecidablePred p] :
    ∀ l : List α, partitionₓ p l = (filterₓ p l, filterₓ (Not ∘ p) l)
  | [] => rfl
  | a :: l => by
    by_cases' pa : p a <;> simp [partition, filter, pa, partition_eq_filter_filter l]

-- sublists
inductive Sublist : List α → List α → Prop
  | slnil : sublist [] []
  | cons (l₁ l₂ a) : sublist l₁ l₂ → sublist l₁ (a :: l₂)
  | cons2 (l₁ l₂ a) : sublist l₁ l₂ → sublist (a :: l₁) (a :: l₂)

-- mathport name: «expr <+ »
infixl:50 " <+ " => Sublist

theorem length_le_of_sublistₓ : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → length l₁ ≤ length l₂
  | _, _, sublist.slnil => le_reflₓ 0
  | _, _, sublist.cons l₁ l₂ a s => le_succ_of_leₓ (length_le_of_sublist s)
  | _, _, sublist.cons2 l₁ l₂ a s => succ_le_succₓ (length_le_of_sublist s)

-- filter
@[simp]
theorem filter_nil (p : α → Prop) [h : DecidablePred p] : filterₓ p [] = [] :=
  rfl

@[simp]
theorem filter_cons_of_pos {p : α → Prop} [h : DecidablePred p] {a : α} :
    ∀ l, p a → filterₓ p (a :: l) = a :: filterₓ p l := fun l pa => if_pos pa

@[simp]
theorem filter_cons_of_neg {p : α → Prop} [h : DecidablePred p] {a : α} :
    ∀ l, ¬p a → filterₓ p (a :: l) = filterₓ p l := fun l pa => if_neg pa

@[simp]
theorem filter_append {p : α → Prop} [h : DecidablePred p] :
    ∀ l₁ l₂ : List α, filterₓ p (l₁ ++ l₂) = filterₓ p l₁ ++ filterₓ p l₂
  | [], l₂ => rfl
  | a :: l₁, l₂ => by
    by_cases' pa : p a <;> simp [pa, filter_append]

@[simp]
theorem filter_sublist {p : α → Prop} [h : DecidablePred p] : ∀ l : List α, filterₓ p l <+ l
  | [] => Sublist.slnil
  | a :: l =>
    if pa : p a then by
      simp [pa] <;> apply sublist.cons2 <;> apply filter_sublist l
    else by
      simp [pa] <;> apply sublist.cons <;> apply filter_sublist l

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

@[simp]
theorem length_map_accumr : ∀ (f : α → σ → σ × β) (x : List α) (s : σ), length (mapAccumr f x s).2 = length x
  | f, a :: x, s => congr_arg succ (length_map_accumr f x s)
  | f, [], s => rfl

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

@[simp]
theorem length_map_accumr₂ :
    ∀ (f : α → β → σ → σ × φ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
  | f, a :: x, b :: y, c =>
    calc
      succ (length (mapAccumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congr_arg succ (length_map_accumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (min_succ_succₓ (length x) (length y))
      
  | f, a :: x, [], c => rfl
  | f, [], b :: y, c => rfl
  | f, [], [], c => rfl

end MapAccumr₂

end List

