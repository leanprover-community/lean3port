
universe u

/--
A difference list is a function that, given a list, returns the original
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

-- error in Data.Dlist: ././Mathport/Syntax/Translate/Basic.lean:265:9: unsupported: advanced prec syntax
local notation `♯`:max := by abstract [] { intros [], simp [] [] [] [] [] [] }

/-- Convert a list to a dlist -/
def of_list (l : List α) : Dlist α :=
  ⟨append l, «expr♯»⟩

/-- Convert a lazily-evaluated list to a dlist -/
def lazy_of_list (l : Thunkₓ (List α)) : Dlist α :=
  ⟨fun xs => l () ++ xs, «expr♯»⟩

/-- Convert a dlist to a list -/
def to_list : Dlist α → List α
| ⟨xs, _⟩ => xs []

/--  Create a dlist containing no elements -/
def Empty : Dlist α :=
  ⟨id, «expr♯»⟩

-- error in Data.Dlist: ././Mathport/Syntax/Translate/Basic.lean:265:9: unsupported: advanced prec syntax
local notation a `::_`:max := list.cons a

/-- Create dlist with a single element -/
def singleton (x : α) : Dlist α :=
  ⟨«expr ::_» x, «expr♯»⟩

attribute [local simp] Function.comp

/-- `O(1)` Prepend a single element to a dlist -/
def cons (x : α) : Dlist α → Dlist α
| ⟨xs, h⟩ =>
  ⟨«expr ::_» x ∘ xs,
    by 
      abstract 
        intros 
        simp 
        rw [←h]⟩

/-- `O(1)` Append a single element to a dlist -/
def concat (x : α) : Dlist α → Dlist α
| ⟨xs, h⟩ =>
  ⟨xs ∘ «expr ::_» x,
    by 
      abstract 
        intros 
        simp 
        rw [h, h [x]]
        simp ⟩

/-- `O(1)` Append dlists -/
protected def append : Dlist α → Dlist α → Dlist α
| ⟨xs, h₁⟩, ⟨ys, h₂⟩ =>
  ⟨xs ∘ ys,
    by 
      intros 
      simp 
      rw [h₂, h₁, h₁ (ys List.nil)]
      simp ⟩

instance : Append (Dlist α) :=
  ⟨Dlist.append⟩

attribute [local simp] of_list to_list Empty singleton cons concat Dlist.append

theorem to_list_of_list (l : List α) : to_list (of_list l) = l :=
  by 
    cases l <;> simp 

-- error in Data.Dlist: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_list_to_list (l : dlist α) : «expr = »(of_list (to_list l), l) :=
begin
  cases [expr l] ["with", ident xs],
  have [ident h] [":", expr «expr = »(append (xs «expr[ , ]»([])), xs)] [],
  { intros [],
    funext [ident x],
    simp [] [] [] ["[", expr l_invariant x, "]"] [] [] },
  simp [] [] [] ["[", expr h, "]"] [] []
end

theorem to_list_empty : to_list (@Empty α) = [] :=
  by 
    simp 

theorem to_list_singleton (x : α) : to_list (singleton x) = [x] :=
  by 
    simp 

theorem to_list_append (l₁ l₂ : Dlist α) : to_list (l₁ ++ l₂) = to_list l₁ ++ to_list l₂ :=
  show to_list (Dlist.append l₁ l₂) = to_list l₁ ++ to_list l₂ from
    by 
      cases l₁ <;> cases l₂ <;> simp  <;> rw [l₁_invariant]

theorem to_list_cons (x : α) (l : Dlist α) : to_list (cons x l) = x :: to_list l :=
  by 
    cases l <;> simp 

theorem to_list_concat (x : α) (l : Dlist α) : to_list (concat x l) = to_list l ++ [x] :=
  by 
    cases l <;> simp  <;> rw [l_invariant]

end Dlist

