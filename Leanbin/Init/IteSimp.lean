prelude
import Leanbin.Init.Data.Bool.Default

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

