/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Control.Lawful

universe u v

/-- A set of elements of type `α`; implemented as a predicate `α → Prop`. -/
def Set (α : Type u) :=
  α → Prop

/-- The set `{x | p x}` of elements satisfying the predicate `p`. -/
def SetOf {α : Type u} (p : α → Prop) : Set α :=
  p

namespace Set

variable {α : Type u}

instance hasMem : Membership α (Set α) :=
  ⟨fun x s => s x⟩

@[simp]
theorem mem_set_of_eq {x : α} {p : α → Prop} : (x ∈ { y | p y }) = p x :=
  rfl

instance : EmptyCollection (Set α) :=
  ⟨{ x | False }⟩

/-- The set that contains all elements of a type. -/
def Univ : Set α :=
  { x | True }

instance : Insert α (Set α) :=
  ⟨fun a s => { b | b = a ∨ b ∈ s }⟩

instance : Singleton α (Set α) :=
  ⟨fun a => { b | b = a }⟩

instance : Sep α (Set α) :=
  ⟨fun p s => { x | x ∈ s ∧ p x }⟩

instance : IsLawfulSingleton α (Set α) :=
  ⟨fun a => funext fun b => propext <| or_falseₓ _⟩

end Set

