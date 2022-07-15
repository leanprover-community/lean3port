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

-- ./././Mathport/Syntax/Translate/Basic.lean:293:40: warning: unsupported option default_priority
/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

universe u

variable {α : Type u}

-- ./././Mathport/Syntax/Translate/Basic.lean:293:40: warning: unsupported option auto_param.check_exists
set_option auto_param.check_exists false

section Preorderₓ

/-!
### Definition of `preorder` and lemmas about types with a `preorder`
-/


/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorderₓ (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by
    run_tac
      order_laws_tac

variable [Preorderₓ α]

/-- The relation `≤` on a preorder is reflexive. -/
@[refl]
theorem le_reflₓ : ∀ a : α, a ≤ a :=
  Preorderₓ.le_refl

/-- The relation `≤` on a preorder is transitive. -/
@[trans]
theorem le_transₓ : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
  Preorderₓ.le_trans

theorem lt_iff_le_not_leₓ : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  Preorderₓ.lt_iff_le_not_le

theorem lt_of_le_not_leₓ : ∀ {a b : α}, a ≤ b → ¬b ≤ a → a < b
  | a, b, hab, hba => lt_iff_le_not_leₓ.mpr ⟨hab, hba⟩

theorem le_not_le_of_ltₓ : ∀ {a b : α}, a < b → a ≤ b ∧ ¬b ≤ a
  | a, b, hab => lt_iff_le_not_leₓ.mp hab

theorem le_of_eqₓ {a b : α} : a = b → a ≤ b := fun h => h ▸ le_reflₓ a

@[trans]
theorem ge_transₓ : ∀ {a b c : α}, a ≥ b → b ≥ c → a ≥ c := fun a b c h₁ h₂ => le_transₓ h₂ h₁

theorem lt_irreflₓ : ∀ a : α, ¬a < a
  | a, haa =>
    match le_not_le_of_ltₓ haa with
    | ⟨h1, h2⟩ => False.ndrec _ (h2 h1)

theorem gt_irreflₓ : ∀ a : α, ¬a > a :=
  lt_irreflₓ

@[trans]
theorem lt_transₓ : ∀ {a b c : α}, a < b → b < c → a < c
  | a, b, c, hab, hbc =>
    match le_not_le_of_ltₓ hab, le_not_le_of_ltₓ hbc with
    | ⟨hab, hba⟩, ⟨hbc, hcb⟩ => lt_of_le_not_leₓ (le_transₓ hab hbc) fun hca => hcb (le_transₓ hca hab)

@[trans]
theorem gt_transₓ : ∀ {a b c : α}, a > b → b > c → a > c := fun a b c h₁ h₂ => lt_transₓ h₂ h₁

theorem ne_of_ltₓ {a b : α} (h : a < b) : a ≠ b := fun he => absurd h (he ▸ lt_irreflₓ a)

theorem ne_of_gtₓ {a b : α} (h : b < a) : a ≠ b := fun he => absurd h (he ▸ lt_irreflₓ a)

theorem lt_asymmₓ {a b : α} (h : a < b) : ¬b < a := fun h1 : b < a => lt_irreflₓ a (lt_transₓ h h1)

theorem le_of_ltₓ : ∀ {a b : α}, a < b → a ≤ b
  | a, b, hab => (le_not_le_of_ltₓ hab).left

@[trans]
theorem lt_of_lt_of_leₓ : ∀ {a b c : α}, a < b → b ≤ c → a < c
  | a, b, c, hab, hbc =>
    let ⟨hab, hba⟩ := le_not_le_of_ltₓ hab
    (lt_of_le_not_leₓ (le_transₓ hab hbc)) fun hca => hba (le_transₓ hbc hca)

@[trans]
theorem lt_of_le_of_ltₓ : ∀ {a b c : α}, a ≤ b → b < c → a < c
  | a, b, c, hab, hbc =>
    let ⟨hbc, hcb⟩ := le_not_le_of_ltₓ hbc
    (lt_of_le_not_leₓ (le_transₓ hab hbc)) fun hca => hcb (le_transₓ hca hab)

@[trans]
theorem gt_of_gt_of_geₓ {a b c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
  lt_of_le_of_ltₓ h₂ h₁

@[trans]
theorem gt_of_ge_of_gtₓ {a b c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
  lt_of_lt_of_leₓ h₂ h₁

theorem not_le_of_gtₓ {a b : α} (h : a > b) : ¬a ≤ b :=
  (le_not_le_of_ltₓ h).right

theorem not_lt_of_geₓ {a b : α} (h : a ≥ b) : ¬a < b := fun hab => not_le_of_gtₓ hab h

theorem le_of_lt_or_eqₓ : ∀ {a b : α}, a < b ∨ a = b → a ≤ b
  | a, b, Or.inl hab => le_of_ltₓ hab
  | a, b, Or.inr hab => hab ▸ le_reflₓ _

theorem le_of_eq_or_ltₓ {a b : α} (h : a = b ∨ a < b) : a ≤ b :=
  Or.elim h le_of_eqₓ le_of_ltₓ

/-- `<` is decidable if `≤` is. -/
def decidableLtOfDecidableLe [@DecidableRel α (· ≤ ·)] : @DecidableRel α (· < ·)
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then is_false fun hab' => not_le_of_gtₓ hab' hba else is_true <| lt_of_le_not_leₓ hab hba
    else is_false fun hab' => hab (le_of_ltₓ hab')

end Preorderₓ

section PartialOrderₓ

/-!
### Definition of `partial_order` and lemmas about types with a partial order
-/


/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrderₓ (α : Type u) extends Preorderₓ α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

variable [PartialOrderₓ α]

theorem le_antisymmₓ : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
  PartialOrderₓ.le_antisymm

theorem le_antisymm_iffₓ {a b : α} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun e => ⟨le_of_eqₓ e, le_of_eqₓ e.symm⟩, fun ⟨h1, h2⟩ => le_antisymmₓ h1 h2⟩

theorem lt_of_le_of_neₓ {a b : α} : a ≤ b → a ≠ b → a < b := fun h₁ h₂ => lt_of_le_not_leₓ h₁ <| mt (le_antisymmₓ h₁) h₂

/-- Equality is decidable if `≤` is. -/
def decidableEqOfDecidableLe [@DecidableRel α (· ≤ ·)] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then if hba : b ≤ a then isTrue (le_antisymmₓ hab hba) else isFalse fun heq => hba (HEq ▸ le_reflₓ _)
    else isFalse fun heq => hab (HEq ▸ le_reflₓ _)

namespace Decidable

variable [@DecidableRel α (· ≤ ·)]

theorem lt_or_eq_of_leₓ {a b : α} (hab : a ≤ b) : a < b ∨ a = b :=
  if hba : b ≤ a then Or.inr (le_antisymmₓ hab hba) else Or.inl (lt_of_le_not_leₓ hab hba)

theorem eq_or_lt_of_leₓ {a b : α} (hab : a ≤ b) : a = b ∨ a < b :=
  (lt_or_eq_of_leₓ hab).swap

theorem le_iff_lt_or_eqₓ {a b : α} : a ≤ b ↔ a < b ∨ a = b :=
  ⟨lt_or_eq_of_leₓ, le_of_lt_or_eqₓ⟩

end Decidable

attribute [local instance] Classical.propDecidable

theorem lt_or_eq_of_leₓ {a b : α} : a ≤ b → a < b ∨ a = b :=
  Decidable.lt_or_eq_of_leₓ

theorem le_iff_lt_or_eqₓ {a b : α} : a ≤ b ↔ a < b ∨ a = b :=
  Decidable.le_iff_lt_or_eqₓ

end PartialOrderₓ

section LinearOrderₓ

/-!
### Definition of `linear_order` and lemmas about types with a linear order
-/


/-- Default definition of `max`. -/
def maxDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if b ≤ a then a else b

/-- Default definition of `min`. -/
def minDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if a ≤ b then a else b

/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`. -/
class LinearOrderₓ (α : Type u) extends PartialOrderₓ α where
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
  decidableLe : DecidableRel (· ≤ ·)
  DecidableEq : DecidableEq α := @decidableEqOfDecidableLe _ _ decidable_le
  decidableLt : DecidableRel ((· < ·) : α → α → Prop) := @decidableLtOfDecidableLe _ _ decidable_le
  max : α → α → α := @maxDefault α _ _
  max_def : max = @maxDefault α _ decidable_le := by
    run_tac
      tactic.interactive.reflexivity
  min : α → α → α := @minDefault α _ _
  min_def : min = @minDefault α _ decidable_le := by
    run_tac
      tactic.interactive.reflexivity

variable [LinearOrderₓ α]

attribute [local instance] LinearOrderₓ.decidableLe

theorem le_totalₓ : ∀ a b : α, a ≤ b ∨ b ≤ a :=
  LinearOrderₓ.le_total

theorem le_of_not_geₓ {a b : α} : ¬a ≥ b → a ≤ b :=
  Or.resolve_left (le_totalₓ b a)

theorem le_of_not_leₓ {a b : α} : ¬a ≤ b → b ≤ a :=
  Or.resolve_left (le_totalₓ a b)

theorem not_lt_of_gtₓ {a b : α} (h : a > b) : ¬a < b :=
  lt_asymmₓ h

theorem lt_trichotomyₓ (a b : α) : a < b ∨ a = b ∨ b < a :=
  Or.elim (le_totalₓ a b)
    (fun h : a ≤ b =>
      Or.elim (Decidable.lt_or_eq_of_leₓ h) (fun h : a < b => Or.inl h) fun h : a = b => Or.inr (Or.inl h))
    fun h : b ≤ a =>
    Or.elim (Decidable.lt_or_eq_of_leₓ h) (fun h : b < a => Or.inr (Or.inr h)) fun h : b = a => Or.inr (Or.inl h.symm)

theorem le_of_not_ltₓ {a b : α} (h : ¬b < a) : a ≤ b :=
  match lt_trichotomyₓ a b with
  | Or.inl hlt => le_of_ltₓ hlt
  | Or.inr (Or.inl HEq) => HEq ▸ le_reflₓ a
  | Or.inr (Or.inr hgt) => absurd hgt h

theorem le_of_not_gtₓ {a b : α} : ¬a > b → a ≤ b :=
  le_of_not_ltₓ

theorem lt_of_not_geₓ {a b : α} (h : ¬a ≥ b) : a < b :=
  lt_of_le_not_leₓ ((le_totalₓ _ _).resolve_right h) h

theorem lt_or_leₓ (a b : α) : a < b ∨ b ≤ a :=
  if hba : b ≤ a then Or.inr hba else Or.inl <| lt_of_not_geₓ hba

theorem le_or_ltₓ (a b : α) : a ≤ b ∨ b < a :=
  (lt_or_leₓ b a).swap

theorem lt_or_geₓ : ∀ a b : α, a < b ∨ a ≥ b :=
  lt_or_leₓ

theorem le_or_gtₓ : ∀ a b : α, a ≤ b ∨ a > b :=
  le_or_ltₓ

theorem lt_or_gt_of_neₓ {a b : α} (h : a ≠ b) : a < b ∨ a > b :=
  match lt_trichotomyₓ a b with
  | Or.inl hlt => Or.inl hlt
  | Or.inr (Or.inl HEq) => absurd HEq h
  | Or.inr (Or.inr hgt) => Or.inr hgt

theorem ne_iff_lt_or_gtₓ {a b : α} : a ≠ b ↔ a < b ∨ a > b :=
  ⟨lt_or_gt_of_neₓ, fun o => Or.elim o ne_of_ltₓ ne_of_gtₓ⟩

theorem lt_iff_not_geₓ (x y : α) : x < y ↔ ¬x ≥ y :=
  ⟨not_le_of_gtₓ, lt_of_not_geₓ⟩

@[simp]
theorem not_ltₓ {a b : α} : ¬a < b ↔ b ≤ a :=
  ⟨le_of_not_gtₓ, not_lt_of_geₓ⟩

@[simp]
theorem not_leₓ {a b : α} : ¬a ≤ b ↔ b < a :=
  (lt_iff_not_geₓ _ _).symm

instance (a b : α) : Decidable (a < b) :=
  LinearOrderₓ.decidableLt a b

instance (a b : α) : Decidable (a ≤ b) :=
  LinearOrderₓ.decidableLe a b

instance (a b : α) : Decidable (a = b) :=
  LinearOrderₓ.decidableEq a b

theorem eq_or_lt_of_not_ltₓ {a b : α} (h : ¬a < b) : a = b ∨ b < a :=
  if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_geₓ fun hge => h (lt_of_le_of_neₓ hge h₁))

instance : IsTotalPreorder α (· ≤ ·) where
  trans := @le_transₓ _ _
  Total := le_totalₓ

-- TODO(Leo): decide whether we should keep this instance or not
instance is_strict_weak_order_of_linear_order : IsStrictWeakOrder α (· < ·) :=
  is_strict_weak_order_of_is_total_preorder lt_iff_not_geₓ

-- TODO(Leo): decide whether we should keep this instance or not
instance is_strict_total_order_of_linear_order : IsStrictTotalOrder α (· < ·) where trichotomous := lt_trichotomyₓ

/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
def ltByCases (x y : α) {P : Sort _} (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
  if h : x < y then h₁ h else if h' : y < x then h₃ h' else h₂ (le_antisymmₓ (le_of_not_gtₓ h') (le_of_not_gtₓ h))

theorem le_imp_le_of_lt_imp_ltₓ {β} [Preorderₓ α] [LinearOrderₓ β] {a b : α} {c d : β} (H : d < c → b < a) (h : a ≤ b) :
    c ≤ d :=
  le_of_not_ltₓ fun h' => not_le_of_gtₓ (H h') h

end LinearOrderₓ

