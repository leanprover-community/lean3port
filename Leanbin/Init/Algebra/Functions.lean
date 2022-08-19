/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import Leanbin.Init.Algebra.Order
import Leanbin.Init.Meta.Default

universe u

section

open Decidable Tactic

variable {α : Type u} [LinearOrder α]

theorem min_def (a b : α) : min a b = if a ≤ b then a else b := by
  rfl

theorem max_def (a b : α) : max a b = if b ≤ a then a else b :=
  match lt_trichotomy a b with
  | .inl h => by simp [max, not_lt_of_gt h, not_le_of_gt h]
  | .inr (.inl rfl) => by simp
  | .inr (.inr h) => by simp [max, h, le_of_lt h]

end

