/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

#align_import data.dlist from "leanprover-community/lean"@"95fa4cfb0a8774570d67bb231c1ab088a94e12bb"

universe u

#print Std.DList /-
/-- A difference list is a function that, given a list, returns the original
contents of the difference list prepended to the given list.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/
structure Std.DList (α : Type u) where
  apply : List α → List α
  invariant : ∀ l, apply l = apply [] ++ l
#align dlist Std.DList
-/

namespace Std.DList

open Function

variable {α : Type u}

local notation:arg "♯" => by abstract intros; simp

#print Std.DList.ofList /-
/-- Convert a list to a dlist -/
def Std.DList.ofList (l : List α) : Std.DList α :=
  ⟨append l, ♯⟩
#align dlist.of_list Std.DList.ofList
-/

#print Std.DList.lazy_ofList /-
/-- Convert a lazily-evaluated list to a dlist -/
def Std.DList.lazy_ofList (l : Thunk (List α)) : Std.DList α :=
  ⟨fun xs => l () ++ xs, ♯⟩
#align dlist.lazy_of_list Std.DList.lazy_ofList
-/

#print Std.DList.toList /-
/-- Convert a dlist to a list -/
def Std.DList.toList : Std.DList α → List α
  | ⟨xs, _⟩ => xs []
#align dlist.to_list Std.DList.toList
-/

#print Std.DList.empty /-
/-- Create a dlist containing no elements -/
def Std.DList.empty : Std.DList α :=
  ⟨id, ♯⟩
#align dlist.empty Std.DList.empty
-/

local notation:arg a "::_" => List.cons a

#print Std.DList.singleton /-
/-- Create dlist with a single element -/
def Std.DList.singleton (x : α) : Std.DList α :=
  ⟨x::_, ♯⟩
#align dlist.singleton Std.DList.singleton
-/

attribute [local simp] Function.comp

#print Std.DList.cons /-
/-- `O(1)` Prepend a single element to a dlist -/
def Std.DList.cons (x : α) : Std.DList α → Std.DList α
  | ⟨xs, h⟩ => ⟨x::_ ∘ xs, by abstract intros; simp; rw [← h]⟩
#align dlist.cons Std.DList.cons
-/

#print Std.DList.push /-
/-- `O(1)` Append a single element to a dlist -/
def Std.DList.push (x : α) : Std.DList α → Std.DList α
  | ⟨xs, h⟩ => ⟨xs ∘ x::_, by abstract intros; simp; rw [h, h [x]]; simp⟩
#align dlist.concat Std.DList.push
-/

#print Std.DList.append /-
/-- `O(1)` Append dlists -/
protected def Std.DList.append : Std.DList α → Std.DList α → Std.DList α
  | ⟨xs, h₁⟩, ⟨ys, h₂⟩ => ⟨xs ∘ ys, by intros; simp; rw [h₂, h₁, h₁ (ys List.nil)]; simp⟩
#align dlist.append Std.DList.append
-/

instance : Append (Std.DList α) :=
  ⟨Std.DList.append⟩

attribute [local simp] of_list to_list Empty singleton cons concat Std.DList.append

#print Std.DList.toList_ofList /-
theorem Std.DList.toList_ofList (l : List α) : Std.DList.toList (Std.DList.ofList l) = l := by
  cases l <;> simp
#align dlist.to_list_of_list Std.DList.toList_ofList
-/

#print Std.DList.ofList_toList /-
theorem Std.DList.ofList_toList (l : Std.DList α) : Std.DList.ofList (Std.DList.toList l) = l :=
  by
  cases' l with xs
  have h : append (xs []) = xs := by intros; funext x; simp [l_invariant x]
  simp [h]
#align dlist.of_list_to_list Std.DList.ofList_toList
-/

#print Std.DList.toList_empty /-
theorem Std.DList.toList_empty : Std.DList.toList (@Std.DList.empty α) = [] := by simp
#align dlist.to_list_empty Std.DList.toList_empty
-/

#print Std.DList.toList_singleton /-
theorem Std.DList.toList_singleton (x : α) : Std.DList.toList (Std.DList.singleton x) = [x] := by
  simp
#align dlist.to_list_singleton Std.DList.toList_singleton
-/

#print Std.DList.toList_append /-
theorem Std.DList.toList_append (l₁ l₂ : Std.DList α) :
    Std.DList.toList (l₁ ++ l₂) = Std.DList.toList l₁ ++ Std.DList.toList l₂ :=
  show Std.DList.toList (Std.DList.append l₁ l₂) = Std.DList.toList l₁ ++ Std.DList.toList l₂ by
    cases l₁ <;> cases l₂ <;> simp <;> rw [l₁_invariant]
#align dlist.to_list_append Std.DList.toList_append
-/

#print Std.DList.toList_cons /-
theorem Std.DList.toList_cons (x : α) (l : Std.DList α) :
    Std.DList.toList (Std.DList.cons x l) = x :: Std.DList.toList l := by cases l <;> simp
#align dlist.to_list_cons Std.DList.toList_cons
-/

#print Std.DList.toList_push /-
theorem Std.DList.toList_push (x : α) (l : Std.DList α) :
    Std.DList.toList (Std.DList.push x l) = Std.DList.toList l ++ [x] := by
  cases l <;> simp <;> rw [l_invariant]
#align dlist.to_list_concat Std.DList.toList_push
-/

end Std.DList

