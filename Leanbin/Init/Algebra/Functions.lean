/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import Leanbin.Init.Algebra.Order
import Leanbin.Init.Meta.Default

universe u

export LinearOrderₓ (min max)

section

open Decidable Tactic

variable {α : Type u} [LinearOrderₓ α]

theorem min_def (a b : α) : min a b = if a ≤ b then a else b := by
  rw [congr_fun LinearOrderₓ.min_def a, minDefault]

theorem max_def (a b : α) : max a b = if b ≤ a then a else b := by
  rw [congr_fun LinearOrderₓ.max_def a, maxDefault]

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
private unsafe def min_tac_step : tactic Unit :=
  solve1 <| (((intros >> sorry) >> try sorry) >> try sorry) >> try sorry

unsafe def tactic.interactive.min_tac (a b : interactive.parse lean.parser.pexpr) : tactic Unit :=
  andthen (interactive.by_cases (none, pquote.1 ((%%ₓa) ≤ %%ₓb))) min_tac_step

theorem min_le_leftₓ (a b : α) : min a b ≤ a :=
  minTac.1 a b

theorem min_le_rightₓ (a b : α) : min a b ≤ b :=
  minTac.1 a b

theorem le_minₓ {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b :=
  minTac.1 a b

theorem le_max_leftₓ (a b : α) : a ≤ max a b :=
  minTac.1 b a

theorem le_max_rightₓ (a b : α) : b ≤ max a b :=
  minTac.1 b a

theorem max_leₓ {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c :=
  minTac.1 b a

theorem eq_minₓ {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀ {d}, d ≤ a → d ≤ b → d ≤ c) : c = min a b :=
  le_antisymmₓ (le_minₓ h₁ h₂) (h₃ (min_le_leftₓ a b) (min_le_rightₓ a b))

theorem min_commₓ (a b : α) : min a b = min b a :=
  eq_minₓ (min_le_rightₓ a b) (min_le_leftₓ a b) fun c h₁ h₂ => le_minₓ h₂ h₁

theorem min_assocₓ (a b c : α) : min (min a b) c = min a (min b c) := by
  apply eq_minₓ
  · apply le_transₓ
    apply min_le_leftₓ
    apply min_le_leftₓ
    
  · apply le_minₓ
    apply le_transₓ
    apply min_le_leftₓ
    apply min_le_rightₓ
    apply min_le_rightₓ
    
  · intro d h₁ h₂
    apply le_minₓ
    apply le_minₓ h₁
    apply le_transₓ h₂
    apply min_le_leftₓ
    apply le_transₓ h₂
    apply min_le_rightₓ
    

theorem min_left_commₓ : ∀ a b c : α, min a (min b c) = min b (min a c) :=
  left_comm (@min α _) (@min_commₓ α _) (@min_assocₓ α _)

@[simp]
theorem min_selfₓ (a : α) : min a a = a :=
  minTac.1 a a

@[ematch]
theorem min_eq_leftₓ {a b : α} (h : a ≤ b) : min a b = a := by
  apply Eq.symm
  apply eq_minₓ (le_reflₓ _) h
  intros
  assumption

@[ematch]
theorem min_eq_rightₓ {a b : α} (h : b ≤ a) : min a b = b :=
  Eq.subst (min_commₓ b a) (min_eq_leftₓ h)

theorem eq_maxₓ {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀ {d}, a ≤ d → b ≤ d → c ≤ d) : c = max a b :=
  le_antisymmₓ (h₃ (le_max_leftₓ a b) (le_max_rightₓ a b)) (max_leₓ h₁ h₂)

theorem max_commₓ (a b : α) : max a b = max b a :=
  eq_maxₓ (le_max_rightₓ a b) (le_max_leftₓ a b) fun c h₁ h₂ => max_leₓ h₂ h₁

theorem max_assocₓ (a b c : α) : max (max a b) c = max a (max b c) := by
  apply eq_maxₓ
  · apply le_transₓ
    apply le_max_leftₓ a b
    apply le_max_leftₓ
    
  · apply max_leₓ
    apply le_transₓ
    apply le_max_rightₓ a b
    apply le_max_leftₓ
    apply le_max_rightₓ
    
  · intro d h₁ h₂
    apply max_leₓ
    apply max_leₓ h₁
    apply le_transₓ (le_max_leftₓ _ _) h₂
    apply le_transₓ (le_max_rightₓ _ _) h₂
    

theorem max_left_commₓ : ∀ a b c : α, max a (max b c) = max b (max a c) :=
  left_comm (@max α _) (@max_commₓ α _) (@max_assocₓ α _)

@[simp]
theorem max_selfₓ (a : α) : max a a = a :=
  minTac.1 a a

theorem max_eq_leftₓ {a b : α} (h : b ≤ a) : max a b = a := by
  apply Eq.symm
  apply eq_maxₓ (le_reflₓ _) h
  intros
  assumption

theorem max_eq_rightₓ {a b : α} (h : a ≤ b) : max a b = b :=
  Eq.subst (max_commₓ b a) (max_eq_leftₓ h)

-- these rely on lt_of_lt
theorem min_eq_left_of_ltₓ {a b : α} (h : a < b) : min a b = a :=
  min_eq_leftₓ (le_of_ltₓ h)

theorem min_eq_right_of_ltₓ {a b : α} (h : b < a) : min a b = b :=
  min_eq_rightₓ (le_of_ltₓ h)

theorem max_eq_left_of_ltₓ {a b : α} (h : b < a) : max a b = a :=
  max_eq_leftₓ (le_of_ltₓ h)

theorem max_eq_right_of_ltₓ {a b : α} (h : a < b) : max a b = b :=
  max_eq_rightₓ (le_of_ltₓ h)

-- these use the fact that it is a linear ordering
theorem lt_minₓ {a b c : α} (h₁ : a < b) (h₂ : a < c) : a < min b c :=
  Or.elim (le_or_gtₓ b c) (fun h : b ≤ c => minTac.1 b c) fun h : b > c => minTac.1 b c

theorem max_ltₓ {a b c : α} (h₁ : a < c) (h₂ : b < c) : max a b < c :=
  Or.elim (le_or_gtₓ a b) (fun h : a ≤ b => minTac.1 b a) fun h : a > b => minTac.1 b a

end

