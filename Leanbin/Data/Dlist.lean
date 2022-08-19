/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.Init.Data.List.Basic

universe u

/-- A difference list is a function that, given a list, returns the original
contents of the difference list prepended to the given list.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/
structure Dlist (α : Type u) where
  apply : List α → List α
  invariant : ∀ l, apply l = apply [] ++ l

namespace Dlist

open Function

variable {α : Type u}

-- mathport name: «expr♯»
local notation:arg "♯" => by
  intros
  simp

/-- Convert a list to a dlist -/
def ofList (l : List α) : Dlist α :=
  ⟨(l ++ ·), ♯⟩

/-- Convert a lazily-evaluated list to a dlist -/
def lazyOfList (l : Thunk (List α)) : Dlist α :=
  ⟨fun xs => l.get ++ xs, ♯⟩

/-- Convert a dlist to a list -/
def toList : Dlist α → List α
  | ⟨xs, _⟩ => xs []

/-- Create a dlist containing no elements -/
def empty : Dlist α :=
  ⟨id, ♯⟩

-- mathport name: «expr ::_»
local notation:arg a "::_" => List.cons a

/-- Create dlist with a single element -/
def singleton (x : α) : Dlist α :=
  ⟨x::_, ♯⟩

attribute [local simp] Function.comp

/-- `O(1)` Prepend a single element to a dlist -/
def cons (x : α) : Dlist α → Dlist α
  | ⟨xs, h⟩ => ⟨x::_ ∘ xs, by simp [← h]⟩

/-- `O(1)` Append a single element to a dlist -/
def concat (x : α) : Dlist α → Dlist α
  | ⟨xs, h⟩ => ⟨xs ∘ x::_, by intros; simp [h (_ :: _)]; rw [List.append_cons]⟩

/-- `O(1)` Append dlists -/
protected def append : Dlist α → Dlist α → Dlist α
  | ⟨xs, h₁⟩, ⟨ys, h₂⟩ =>
    ⟨xs ∘ ys, fun l => by
      simp only [comp]
      rw [h₂, h₁, h₁ (ys List.nil), List.append_assoc]⟩

instance : Append (Dlist α) :=
  ⟨Dlist.append⟩

attribute [local simp] ofList toList empty singleton cons concat Dlist.append

theorem to_list_of_list (l : List α) : toList (ofList l) = l := by
  cases l <;> simp

theorem of_list_to_list (l : Dlist α) : ofList (toList l) = l := by
  simp [← invariant l]

theorem to_list_empty : toList (@empty α) = [] := by
  simp

theorem to_list_singleton (x : α) : toList (singleton x) = [x] := by
  simp

theorem to_list_append (l₁ l₂ : Dlist α) : toList (l₁ ++ l₂) = toList l₁ ++ toList l₂ := by
  simp [← invariant l₁]

theorem to_list_cons (x : α) (l : Dlist α) : toList (cons x l) = x :: toList l := by
  simp

theorem to_list_concat (x : α) (l : Dlist α) : toList (concat x l) = toList l ++ [x] := by
  simp [← invariant l]

end Dlist

