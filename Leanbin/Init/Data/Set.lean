/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib

universe u v

/-- The set `{x | p x}` of elements satisfying the predicate `p`. -/
abbrev SetOf := @setOf

namespace Set

@[simp]
theorem mem_set_of_eq {x : α} {p : α → Prop} : (x ∈ { y | p y }) = p x :=
  rfl

/-- The set that contains all elements of a type. -/
abbrev Univ : Set α := Set.univ
