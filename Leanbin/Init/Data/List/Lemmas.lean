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

@[simp]
theorem length_repeat (a : α) (n : ℕ) : length («repeat» a n) = n := by
  induction n <;> simp [*] <;> rfl

-- list subset
protected abbrev Subset (l₁ l₂ : List α) := List.subset l₁ l₂

@[refl, simp]
theorem Subset.refl (l : List α) : l ⊆ l := fun b i => i

@[trans]
theorem Subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ := fun b i => h₂ (h₁ i)

theorem length_remove_nth : ∀ (l : List α) (i : ℕ), i < length l → length (removeNth l i) = length l - 1 :=
  length_removeNth

-- sublists
abbrev Sublist : List α → List α → Prop := sublist

-- filter
@[simp]
theorem filter_nil (p : α → Bool) : filter p [] = [] :=
  rfl

@[simp]
theorem filter_cons_of_pos {p : α → Bool} {a : α} :
    ∀ l, p a → filter p (a :: l) = a :: filter p l :=
  fun l pa => by simp [List.filter, pa]

@[simp]
theorem filter_cons_of_neg {p : α → Bool} {a : α} :
    ∀ l, ¬p a → filter p (a :: l) = filter p l :=
  fun l pa => by simp [List.filter, pa]

@[simp]
theorem filter_append {p : α → Bool} :
    ∀ l₁ l₂ : List α, filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂
  | [], l₂ => rfl
  | a :: l₁, l₂ => by
    by_cases pa : p a <;> simp [pa, ← filter_append]

@[simp]
theorem filter_sublist {p : α → Bool} : ∀ l : List α, filter p l <+ l
  | [] => sublist.slnil
  | a :: l =>
    if pa : p a then by
      simp [pa] <;> apply sublist.cons2 <;> apply filter_sublist l
    else by
      simp [pa] <;> apply sublist.cons <;> apply filter_sublist l

@[simp]
theorem partitionAux_eq_filter_filter (p : α → Bool) :
    ∀ l : List α, partitionAux p l (a, b) = (a.reverse ++ filter p l, b.reverse ++ filter (! p ·) l)
  | [] => by simp [partitionAux]
  | x::xs => by by_cases h : p x <;> simp [partitionAux, h, partitionAux_eq_filter_filter p xs, ← List.append_cons]

@[simp]
theorem partition_eq_filter_filter (p : α → Bool) (l : List α) : partition p l = (filter p l, filter (! p ·) l) :=
  partitionAux_eq_filter_filter p l

-- map_accumr
section MapAccumr

variable {φ : Type w₁} {σ : Type w₂}

-- This runs a function over a list returning the intermediate results and a
-- a final result.
def mapAccumr (f : α → σ → σ × β) : List α → σ → σ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := mapAccumr f yr c
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
    let r := mapAccumr₂ f xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)

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

end MapAccumr₂

end List

