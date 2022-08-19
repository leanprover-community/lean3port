/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.List.Basic
import Leanbin.Init.Data.Char.Basic

namespace String

instance : LT String :=
  ⟨fun s₁ s₂ => s₁.data < s₂.data⟩

instance hasDecidableLt (s₁ s₂ : String) : Decidable (s₁ < s₂) :=
  List.hasDecidableLt s₁.data s₂.data

abbrev empty : String := ""

def fold {α} (a : α) (f : α → Char → α) (s : String) : α :=
  s.foldl f a

namespace Iterator

def nextToString : Iterator → String
  | it => it.remainingToString

def prevToString : Iterator → String
  | ⟨p, n⟩ => p.extract 0 n

def insert : Iterator → String → Iterator
  | it, s => ⟨it.prevToString ++ s ++ it.remainingToString, it.i⟩

def remove : Iterator → Nat → Iterator
  | it, m => ⟨it.prevToString ++ (it.forward m).remainingToString, it.i⟩

end Iterator

def popBack (s : String) : String :=
  s.mkIterator.toEnd.prev.prevToString

def popnBack (s : String) (n : Nat) : String :=
  (s.mkIterator.toEnd.prevn n).prevToString

def backn (s : String) (n : Nat) : String :=
  (s.mkIterator.toEnd.prevn n).nextToString

end String

private def toNatCore : String.Iterator → Nat → Nat → Nat
  | it, 0, r => r
  | it, i + 1, r =>
    let c := it.curr
    let r := r * 10 + c.toNat - '0'.toNat
    toNatCore it.next i r

def String.toNat (s : String) : Nat :=
  toNatCore s.mkIterator s.length 0

@[simp]
theorem String.length_push : (String.push s c).length = s.length + 1 := by
  cases s <;> simp [String.push, String.length]

@[simp]
theorem String.length_empty : "".length = 0 := rfl

@[simp]
theorem List.getLast!_append [Inhabited α] {y : α} : (xs ++ [y]).getLast! = y := by
  have : ∀ x y : α, ∀ xs, getLast (x :: (xs ++ [y])) (by simp) = y := by
    simp only [← cons_append, getLast_append]
    exact default
  cases xs <;> simp [this]

@[simp]
theorem List.append_singleton_eq_iff {x y : α} : xs ++ [x] = ys ++ [y] ↔ xs = ys ∧ x = y := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x' xs ih => cases ys with
    | nil => simp
    | cons y' ys => constructor <;> simp_all [ih]

theorem String.ext_iff (s t : String) : s = t ↔ s.data = t.data :=
  ⟨congrArg _, fun h => by cases s; cases t; subst h; rfl⟩

@[simp]
theorem String.push_eq_push : String.push s₁ c₁ = String.push s₂ c₂ ↔ s₁ = s₂ ∧ c₁ = c₂ := by
  cases s₁ <;> cases s₂ <;> simp [String.push, String.ext_iff]

attribute [simp] String.str String.empty

namespace String

theorem empty_ne_push (c : Char) (s : String) : "" ≠ String.push s c :=
  mt (congrArg String.length) (by simp (config := {arith := true}))

theorem empty_ne_str (c : Char) (s : String) : String.empty ≠ String.str s c :=
  empty_ne_push c s

theorem str_ne_empty (c : Char) (s : String) : String.str s c ≠ .empty :=
  (empty_ne_str c s).symm

theorem str_ne_str_left : ∀ {c₁ c₂ : Char} (s₁ s₂ : String), c₁ ≠ c₂ → String.str s₁ c₁ ≠ String.str s₂ c₂
  | c₁, c₂, s₁, s₂, h => by simp [h]

theorem str_ne_str_right : ∀ (c₁ c₂ : Char) {s₁ s₂ : String}, s₁ ≠ s₂ → String.str s₁ c₁ ≠ String.str s₂ c₂
  | c₁, c₂, s₁, s₂, h => by simp [h]

end String

