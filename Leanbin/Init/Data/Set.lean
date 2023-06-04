/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.set
! leanprover-community/lean commit ab343ab4edc491dbd02bed7b70295a0bb88be06f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Control.Lawful

universe u v

#print Set /-
/-- A set of elements of type `α`; implemented as a predicate `α → Prop`. -/
def Set (α : Type u) :=
  α → Prop
#align set Set
-/

#print setOf /-
/-- The set `{x | p x}` of elements satisfying the predicate `p`. -/
def setOf {α : Type u} (p : α → Prop) : Set α :=
  p
#align set_of setOf
-/

namespace Set

variable {α : Type u}

instance hasMem : Membership α (Set α) :=
  ⟨fun x s => s x⟩
#align set.has_mem Set.hasMem

#print Set.mem_setOf_eq /-
@[simp]
theorem mem_setOf_eq {x : α} {p : α → Prop} : (x ∈ {y | p y}) = p x :=
  rfl
#align set.mem_set_of_eq Set.mem_setOf_eq
-/

instance : EmptyCollection (Set α) :=
  ⟨{x | False}⟩

#print Set.univ /-
/-- The set that contains all elements of a type. -/
def univ : Set α :=
  {x | True}
#align set.univ Set.univ
-/

instance : Insert α (Set α) :=
  ⟨fun a s => {b | b = a ∨ b ∈ s}⟩

instance : Singleton α (Set α) :=
  ⟨fun a => {b | b = a}⟩

instance : Sep α (Set α) :=
  ⟨fun p s => {x | x ∈ s ∧ p x}⟩

instance : IsLawfulSingleton α (Set α) :=
  ⟨fun a => funext fun b => propext <| or_false_iff _⟩

end Set

