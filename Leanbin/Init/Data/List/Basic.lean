/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.Bool.Basic
import Leanbin.Init.Propext

open Decidable List

universe u v w

instance (α : Type u) : Inhabited (List α) :=
  ⟨List.nil⟩

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

def empty : List α → Bool
  | [] => true
  | _ :: _ => false

open Option Nat

@[simp]
def nth : List α → Nat → Option α
  | [], n => none
  | a :: l, 0 => some a
  | a :: l, n + 1 => nth l n

@[simp]
def nthLe : ∀ (l : List α) (n), n < l.length → α
  | [], n, h => absurd h n.not_lt_zero
  | a :: l, 0, h => a
  | a :: l, n + 1, h => nthLe l n (le_of_succ_le_succ h)

def mapWithIndexCore (f : ℕ → α → β) : ℕ → List α → List β
  | k, [] => []
  | k, a :: as => f k a :: mapWithIndexCore f (k + 1) as

/-- Given a function `f : ℕ → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`. -/
def mapWithIndex (f : ℕ → α → β) (as : List α) : List β :=
  mapWithIndexCore f 0 as

def findIndex (p : α → Prop) [DecidablePred p] : List α → Nat
  | [] => 0
  | a :: l => if p a then 0 else succ (findIndex p l)

def updateNth : List α → ℕ → α → List α
  | x :: xs, 0, a => a :: xs
  | x :: xs, i + 1, a => x :: updateNth xs i a
  | [], _, _ => []

instance [DecidableEq α] : Insert α (List α) :=
  ⟨List.insert⟩

instance : Singleton α (List α) :=
  ⟨fun x => [x]⟩

-- TODO
-- instance [DecidableEq α] : IsLawfulSingleton α (List α) :=
--   ⟨fun x => show (if x ∈ ([] : List α) then [] else [x]) = [x] from if_neg not_false⟩

@[simp]
def «repeat» (a : α) : ℕ → List α
  | 0 => []
  | succ n => a :: «repeat» a n

@[simp]
def last : ∀ l : List α, l ≠ [] → α
  | [], h => absurd rfl h
  | [a], h => a
  | a :: b :: l, h => last (b :: l) fun h => List.noConfusion h

def ilast [Inhabited α] : List α → α
  | [] => arbitrary α
  | [a] => a
  | [a, b] => b
  | a :: b :: l => ilast l

@[inline]
protected def ret {α : Type u} (a : α) : List α :=
  [a]

theorem le_eq_not_gt [LT α] : ∀ l₁ l₂ : List α, (l₁ ≤ l₂) = ¬l₂ < l₁ := fun l₁ l₂ => rfl

theorem lt_eq_not_ge [LT α] [DecidableRel ((· < ·) : α → α → Prop)] : ∀ l₁ l₂ : List α, (l₁ < l₂) = ¬l₂ ≤ l₁ :=
  fun l₁ l₂ => show (l₁ < l₂) = ¬¬l₁ < l₂ from Eq.subst (propext (not_not_iff (l₁ < l₂))).symm rfl

end List

