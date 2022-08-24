/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Bool.Default

/-
Simplification lemmas for ite.

We don't prove them at logic.lean because it is easier to prove them using
the tactic framework.
-/
/-
Simplification lemmas for ite.

We don't prove them at logic.lean because it is easier to prove them using
the tactic framework.
-/
@[simp]
theorem if_true_right_eq_or (p : Prop) [h : Decidable p] (q : Prop) : (if p then q else True) = (¬p ∨ q) := by
  by_cases' p <;> simp [h]

@[simp]
theorem if_true_left_eq_or (p : Prop) [h : Decidable p] (q : Prop) : (if p then True else q) = (p ∨ q) := by
  by_cases' p <;> simp [h]

@[simp]
theorem if_false_right_eq_and (p : Prop) [h : Decidable p] (q : Prop) : (if p then q else False) = (p ∧ q) := by
  by_cases' p <;> simp [h]

@[simp]
theorem if_false_left_eq_and (p : Prop) [h : Decidable p] (q : Prop) : (if p then False else q) = (¬p ∧ q) := by
  by_cases' p <;> simp [h]

