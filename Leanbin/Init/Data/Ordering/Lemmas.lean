/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Ordering.Basic
import Leanbin.Init.Meta.Default
import Leanbin.Init.Algebra.Classes
import Leanbin.Init.IteSimp

-- ./././Mathport/Syntax/Translate/Basic.lean:293:40: warning: unsupported option default_priority
set_option default_priority 100

universe u

namespace Ordering

@[simp]
theorem ite_eq_lt_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = Ordering.lt) = if c then a = Ordering.lt else b = Ordering.lt := by
  by_cases' c <;> simp [*]

@[simp]
theorem ite_eq_eq_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = Ordering.eq) = if c then a = Ordering.eq else b = Ordering.eq := by
  by_cases' c <;> simp [*]

@[simp]
theorem ite_eq_gt_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = Ordering.gt) = if c then a = Ordering.gt else b = Ordering.gt := by
  by_cases' c <;> simp [*]

-- ------------------------------------------------------------------
end Ordering

section

variable {α : Type u} {lt : α → α → Prop} [DecidableRel lt]

attribute [local simp] cmpUsing

@[simp]
theorem cmp_using_eq_lt (a b : α) : (cmpUsing lt a b = Ordering.lt) = lt a b := by
  simp

@[simp]
theorem cmp_using_eq_gt [IsStrictOrder α lt] (a b : α) : (cmpUsing lt a b = Ordering.gt) = lt b a := by
  simp
  apply propext
  apply Iff.intro
  · exact fun h => h.2
    
  · intro hba
    constructor
    · intro hab
      exact absurd (trans hab hba) (irrefl a)
      
    · assumption
      
    

@[simp]
theorem cmp_using_eq_eq (a b : α) : (cmpUsing lt a b = Ordering.eq) = (¬lt a b ∧ ¬lt b a) := by
  simp

end

