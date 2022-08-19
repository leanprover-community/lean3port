/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Classical
import Leanbin.Init.Meta.Name
import Leanbin.Init.Algebra.Classes

universe u

variable {α : Type u}

section Preorder

/-!
### Definition of `preorder` and lemmas about types with a `preorder`
-/


variable [Preorder α]

/-- `<` is decidable if `≤` is. -/
def decidableLtOfDecidableLe [@DecidableRel α (· ≤ ·)] : @DecidableRel α (· < ·)
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isFalse fun hab' => not_le_of_gt hab' hba else isTrue <| lt_of_le_not_le hab hba
    else isFalse fun hab' => hab (le_of_lt hab')

end Preorder

section PartialOrder

/-!
### Definition of `partial_order` and lemmas about types with a partial order
-/

variable [PartialOrder α]

/-- Equality is decidable if `≤` is. -/
def decidableEqOfDecidableLe [@DecidableRel α (· ≤ ·)] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then if hba : b ≤ a then isTrue (le_antisymm hab hba) else isFalse fun heq => hba (heq ▸ le_refl _)
    else isFalse fun heq => hab (heq ▸ le_refl _)


end PartialOrder

section LinearOrder

/-!
### Definition of `linear_order` and lemmas about types with a linear order
-/

/-- Default definition of `max`. -/
def maxDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if b ≤ a then a else b

/-- Default definition of `min`. -/
def minDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if a ≤ b then a else b

variable [LinearOrder α]

instance : IsTotalPreorder α (· ≤ ·) where
  trans := @le_trans _ _
  Total := le_total

-- TODO(Leo): decide whether we should keep this instance or not
instance is_strict_weak_order_of_linear_order : IsStrictWeakOrder α (· < ·) :=
  is_strict_weak_order_of_is_total_preorder (le := (· ≤ ·)) lt_iff_not_ge

-- TODO(Leo): decide whether we should keep this instance or not
instance is_strict_total_order_of_linear_order : IsStrictTotalOrder α (· < ·) where trichotomous := lt_trichotomy

/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
def ltByCases (x y : α) {P : Sort _} (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
  if h : x < y then h₁ h else if h' : y < x then h₃ h' else h₂ (le_antisymm (le_of_not_gt h') (le_of_not_gt h))

end LinearOrder

