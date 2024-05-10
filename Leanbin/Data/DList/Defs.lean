/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

#align_import data.dlist from "leanprover-community/lean"@"95fa4cfb0a8774570d67bb231c1ab088a94e12bb"

universe u

#print Batteries.DList /-
/-- A difference list is a function that, given a list, returns the original
contents of the difference list prepended to the given list.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/
structure Batteries.DList (α : Type u) where
  apply : List α → List α
  invariant : ∀ l, apply l = apply [] ++ l
#align dlist Batteries.DList
-/

namespace Batteries.DList

open Function

variable {α : Type u}

local notation:arg "♯" => by abstract intros; simp

#print Batteries.DList.ofList /-
/-- Convert a list to a dlist -/
def Batteries.DList.ofList (l : List α) : Batteries.DList α :=
  ⟨append l, ♯⟩
#align dlist.of_list Batteries.DList.ofList
-/

#print Batteries.DList.lazy_ofList /-
/-- Convert a lazily-evaluated list to a dlist -/
def Batteries.DList.lazy_ofList (l : Thunk (List α)) : Batteries.DList α :=
  ⟨fun xs => l () ++ xs, ♯⟩
#align dlist.lazy_of_list Batteries.DList.lazy_ofList
-/

#print Batteries.DList.toList /-
/-- Convert a dlist to a list -/
def Batteries.DList.toList : Batteries.DList α → List α
  | ⟨xs, _⟩ => xs []
#align dlist.to_list Batteries.DList.toList
-/

#print Batteries.DList.empty /-
/-- Create a dlist containing no elements -/
def Batteries.DList.empty : Batteries.DList α :=
  ⟨id, ♯⟩
#align dlist.empty Batteries.DList.empty
-/

local notation:arg a "::_" => List.cons a

#print Batteries.DList.singleton /-
/-- Create dlist with a single element -/
def Batteries.DList.singleton (x : α) : Batteries.DList α :=
  ⟨x::_, ♯⟩
#align dlist.singleton Batteries.DList.singleton
-/

attribute [local simp] Function.comp

#print Batteries.DList.cons /-
/-- `O(1)` Prepend a single element to a dlist -/
def Batteries.DList.cons (x : α) : Batteries.DList α → Batteries.DList α
  | ⟨xs, h⟩ => ⟨x::_ ∘ xs, by abstract intros; simp; rw [← h]⟩
#align dlist.cons Batteries.DList.cons
-/

#print Batteries.DList.push /-
/-- `O(1)` Append a single element to a dlist -/
def Batteries.DList.push (x : α) : Batteries.DList α → Batteries.DList α
  | ⟨xs, h⟩ => ⟨xs ∘ x::_, by abstract intros; simp; rw [h, h [x]]; simp⟩
#align dlist.concat Batteries.DList.push
-/

#print Batteries.DList.append /-
/-- `O(1)` Append dlists -/
protected def Batteries.DList.append : Batteries.DList α → Batteries.DList α → Batteries.DList α
  | ⟨xs, h₁⟩, ⟨ys, h₂⟩ => ⟨xs ∘ ys, by intros; simp; rw [h₂, h₁, h₁ (ys List.nil)]; simp⟩
#align dlist.append Batteries.DList.append
-/

instance : Append (Batteries.DList α) :=
  ⟨Batteries.DList.append⟩

attribute [local simp] of_list to_list Empty singleton cons concat Batteries.DList.append

#print Batteries.DList.toList_ofList /-
theorem Batteries.DList.toList_ofList (l : List α) :
    Batteries.DList.toList (Batteries.DList.ofList l) = l := by cases l <;> simp
#align dlist.to_list_of_list Batteries.DList.toList_ofList
-/

#print Batteries.DList.ofList_toList /-
theorem Batteries.DList.ofList_toList (l : Batteries.DList α) :
    Batteries.DList.ofList (Batteries.DList.toList l) = l :=
  by
  cases' l with xs
  have h : append (xs []) = xs := by intros; funext x; simp [l_invariant x]
  simp [h]
#align dlist.of_list_to_list Batteries.DList.ofList_toList
-/

#print Batteries.DList.toList_empty /-
theorem Batteries.DList.toList_empty : Batteries.DList.toList (@Batteries.DList.empty α) = [] := by
  simp
#align dlist.to_list_empty Batteries.DList.toList_empty
-/

#print Batteries.DList.toList_singleton /-
theorem Batteries.DList.toList_singleton (x : α) :
    Batteries.DList.toList (Batteries.DList.singleton x) = [x] := by simp
#align dlist.to_list_singleton Batteries.DList.toList_singleton
-/

#print Batteries.DList.toList_append /-
theorem Batteries.DList.toList_append (l₁ l₂ : Batteries.DList α) :
    Batteries.DList.toList (l₁ ++ l₂) = Batteries.DList.toList l₁ ++ Batteries.DList.toList l₂ :=
  show
    Batteries.DList.toList (Batteries.DList.append l₁ l₂) =
      Batteries.DList.toList l₁ ++ Batteries.DList.toList l₂
    by cases l₁ <;> cases l₂ <;> simp <;> rw [l₁_invariant]
#align dlist.to_list_append Batteries.DList.toList_append
-/

#print Batteries.DList.toList_cons /-
theorem Batteries.DList.toList_cons (x : α) (l : Batteries.DList α) :
    Batteries.DList.toList (Batteries.DList.cons x l) = x :: Batteries.DList.toList l := by
  cases l <;> simp
#align dlist.to_list_cons Batteries.DList.toList_cons
-/

#print Batteries.DList.toList_push /-
theorem Batteries.DList.toList_push (x : α) (l : Batteries.DList α) :
    Batteries.DList.toList (Batteries.DList.push x l) = Batteries.DList.toList l ++ [x] := by
  cases l <;> simp <;> rw [l_invariant]
#align dlist.to_list_concat Batteries.DList.toList_push
-/

end Batteries.DList

