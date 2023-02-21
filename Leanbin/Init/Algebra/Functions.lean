/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

! This file was ported from Lean 3 source module init.algebra.functions
! leanprover-community/mathlib commit c2bcdbcbe741ed37c361a30d38e179182b989f76
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Algebra.Order
import Leanbin.Init.Meta.Default

universe u

export LinearOrder (min max)

section

open Decidable Tactic

variable {α : Type u} [LinearOrder α]

/- warning: min_def -> min_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 a b) (ite.{succ u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (LE.le.decidable.{u1} α _inst_1 a b) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) (ite.{succ u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (instDecidableLeToLEToPreorderToPartialOrder.{u1} α _inst_1 a b) a b)
Case conversion may be inaccurate. Consider using '#align min_def min_defₓ'. -/
theorem min_def (a b : α) : min a b = if a ≤ b then a else b := by
  rw [congr_fun LinearOrder.min_def a, minDefault]
#align min_def min_def

/- warning: max_def -> max_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 a b) (ite.{succ u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (LE.le.decidable.{u1} α _inst_1 a b) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) (ite.{succ u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (instDecidableLeToLEToPreorderToPartialOrder.{u1} α _inst_1 a b) b a)
Case conversion may be inaccurate. Consider using '#align max_def max_defₓ'. -/
theorem max_def (a b : α) : max a b = if a ≤ b then b else a := by
  rw [congr_fun LinearOrder.max_def a, maxDefault]
#align max_def max_def

/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def min_tac_step : tactic Unit :=
  solve1 <| (((intros >> sorry) >> try sorry) >> try sorry) >> try sorry
#align min_tac_step min_tac_step

-- failed to format: unknown constant 'term.pseudo.antiquot'
unsafe
  def
    tactic.interactive.min_tac
    ( a b : interactive.parse lean.parser.pexpr ) : tactic Unit
    := andthen ( interactive.by_cases ( none , ` `( $ ( a ) ≤ $ ( b ) ) ) ) min_tac_step
#align tactic.interactive.min_tac tactic.interactive.min_tac

/- warning: min_le_left -> min_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) (LinearOrder.min.{u1} α _inst_1 a b) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) a
Case conversion may be inaccurate. Consider using '#align min_le_left min_le_leftₓ'. -/
theorem min_le_left (a b : α) : min a b ≤ a :=
  minTac.1 a b
#align min_le_left min_le_left

/- warning: min_le_right -> min_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) (LinearOrder.min.{u1} α _inst_1 a b) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) b
Case conversion may be inaccurate. Consider using '#align min_le_right min_le_rightₓ'. -/
theorem min_le_right (a b : α) : min a b ≤ b :=
  minTac.1 a b
#align min_le_right min_le_right

/- warning: le_min -> le_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c (LinearOrder.min.{u1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align le_min le_minₓ'. -/
theorem le_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b :=
  minTac.1 a b
#align le_min le_min

/- warning: le_max_left -> le_max_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a (LinearOrder.max.{u1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align le_max_left le_max_leftₓ'. -/
theorem le_max_left (a b : α) : a ≤ max a b :=
  minTac.1 a b
#align le_max_left le_max_left

/- warning: le_max_right -> le_max_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b (LinearOrder.max.{u1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align le_max_right le_max_rightₓ'. -/
theorem le_max_right (a b : α) : b ≤ max a b :=
  minTac.1 a b
#align le_max_right le_max_right

/- warning: max_le -> max_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) (LinearOrder.max.{u1} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) c)
Case conversion may be inaccurate. Consider using '#align max_le max_leₓ'. -/
theorem max_le {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c :=
  minTac.1 a b
#align max_le max_le

/- warning: eq_min -> eq_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c b) -> (forall {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) d a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) d b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) d c)) -> (Eq.{succ u1} α c (LinearOrder.min.{u1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c b) -> (forall {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) d a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) d b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) d c)) -> (Eq.{succ u1} α c (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align eq_min eq_minₓ'. -/
theorem eq_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀ {d}, d ≤ a → d ≤ b → d ≤ c) :
    c = min a b :=
  le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))
#align eq_min eq_min

/- warning: min_comm -> min_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 a b) (LinearOrder.min.{u1} α _inst_1 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align min_comm min_commₓ'. -/
theorem min_comm (a b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) fun c h₁ h₂ => le_min h₂ h₁
#align min_comm min_comm

/- warning: min_assoc -> min_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 (LinearOrder.min.{u1} α _inst_1 a b) c) (LinearOrder.min.{u1} α _inst_1 a (LinearOrder.min.{u1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) c) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align min_assoc min_assocₓ'. -/
theorem min_assoc (a b c : α) : min (min a b) c = min a (min b c) :=
  by
  apply eq_min
  · apply le_trans
    apply min_le_left
    apply min_le_left
  · apply le_min
    apply le_trans
    apply min_le_left
    apply min_le_right
    apply min_le_right
  · intro d h₁ h₂
    apply le_min
    apply le_min h₁
    apply le_trans h₂
    apply min_le_left
    apply le_trans h₂
    apply min_le_right
#align min_assoc min_assoc

/- warning: min_left_comm -> min_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 a (LinearOrder.min.{u1} α _inst_1 b c)) (LinearOrder.min.{u1} α _inst_1 b (LinearOrder.min.{u1} α _inst_1 a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α], LeftCommutative.{u1, u1} α α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align min_left_comm min_left_commₓ'. -/
theorem min_left_comm : ∀ a b c : α, min a (min b c) = min b (min a c) :=
  left_comm (@min α _) (@min_comm α _) (@min_assoc α _)
#align min_left_comm min_left_comm

/- warning: min_self -> min_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 a a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a a) a
Case conversion may be inaccurate. Consider using '#align min_self min_selfₓ'. -/
@[simp]
theorem min_self (a : α) : min a a = a :=
  minTac.1 a a
#align min_self min_self

/- warning: min_eq_left -> min_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) a)
Case conversion may be inaccurate. Consider using '#align min_eq_left min_eq_leftₓ'. -/
@[ematch]
theorem min_eq_left {a b : α} (h : a ≤ b) : min a b = a := by apply Eq.symm;
  apply eq_min (le_refl _) h; intros ; assumption
#align min_eq_left min_eq_left

/- warning: min_eq_right -> min_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a) -> (Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a) -> (Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) b)
Case conversion may be inaccurate. Consider using '#align min_eq_right min_eq_rightₓ'. -/
@[ematch]
theorem min_eq_right {a b : α} (h : b ≤ a) : min a b = b :=
  Eq.subst (min_comm b a) (min_eq_left h)
#align min_eq_right min_eq_right

/- warning: eq_max -> eq_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b c) -> (forall {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c d)) -> (Eq.{succ u1} α c (LinearOrder.max.{u1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b c) -> (forall {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) c d)) -> (Eq.{succ u1} α c (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align eq_max eq_maxₓ'. -/
theorem eq_max {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀ {d}, a ≤ d → b ≤ d → c ≤ d) :
    c = max a b :=
  le_antisymm (h₃ (le_max_left a b) (le_max_right a b)) (max_le h₁ h₂)
#align eq_max eq_max

/- warning: max_comm -> max_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 a b) (LinearOrder.max.{u1} α _inst_1 b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align max_comm max_commₓ'. -/
theorem max_comm (a b : α) : max a b = max b a :=
  eq_max (le_max_right a b) (le_max_left a b) fun c h₁ h₂ => max_le h₂ h₁
#align max_comm max_comm

/- warning: max_assoc -> max_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 (LinearOrder.max.{u1} α _inst_1 a b) c) (LinearOrder.max.{u1} α _inst_1 a (LinearOrder.max.{u1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) c) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align max_assoc max_assocₓ'. -/
theorem max_assoc (a b c : α) : max (max a b) c = max a (max b c) :=
  by
  apply eq_max
  · apply le_trans
    apply le_max_left a b
    apply le_max_left
  · apply max_le
    apply le_trans
    apply le_max_right a b
    apply le_max_left
    apply le_max_right
  · intro d h₁ h₂
    apply max_le
    apply max_le h₁
    apply le_trans (le_max_left _ _) h₂
    apply le_trans (le_max_right _ _) h₂
#align max_assoc max_assoc

/- warning: max_left_comm -> max_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 a (LinearOrder.max.{u1} α _inst_1 b c)) (LinearOrder.max.{u1} α _inst_1 b (LinearOrder.max.{u1} α _inst_1 a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) b c)) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) b (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align max_left_comm max_left_commₓ'. -/
theorem max_left_comm : ∀ a b c : α, max a (max b c) = max b (max a c) :=
  left_comm (@max α _) (@max_comm α _) (@max_assoc α _)
#align max_left_comm max_left_comm

/- warning: max_self -> max_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 a a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α), Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a a) a
Case conversion may be inaccurate. Consider using '#align max_self max_selfₓ'. -/
@[simp]
theorem max_self (a : α) : max a a = a :=
  minTac.1 a a
#align max_self max_self

/- warning: max_eq_left -> max_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a) -> (Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a) -> (Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) a)
Case conversion may be inaccurate. Consider using '#align max_eq_left max_eq_leftₓ'. -/
theorem max_eq_left {a b : α} (h : b ≤ a) : max a b = a := by apply Eq.symm;
  apply eq_max (le_refl _) h; intros ; assumption
#align max_eq_left max_eq_left

/- warning: max_eq_right -> max_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) b)
Case conversion may be inaccurate. Consider using '#align max_eq_right max_eq_rightₓ'. -/
theorem max_eq_right {a b : α} (h : a ≤ b) : max a b = b :=
  Eq.subst (max_comm b a) (max_eq_left h)
#align max_eq_right max_eq_right

/- warning: min_eq_left_of_lt -> min_eq_left_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) a)
Case conversion may be inaccurate. Consider using '#align min_eq_left_of_lt min_eq_left_of_ltₓ'. -/
-- these rely on lt_of_lt
theorem min_eq_left_of_lt {a b : α} (h : a < b) : min a b = a :=
  min_eq_left (le_of_lt h)
#align min_eq_left_of_lt min_eq_left_of_lt

/- warning: min_eq_right_of_lt -> min_eq_right_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a) -> (Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a) -> (Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) b)
Case conversion may be inaccurate. Consider using '#align min_eq_right_of_lt min_eq_right_of_ltₓ'. -/
theorem min_eq_right_of_lt {a b : α} (h : b < a) : min a b = b :=
  min_eq_right (le_of_lt h)
#align min_eq_right_of_lt min_eq_right_of_lt

/- warning: max_eq_left_of_lt -> max_eq_left_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a) -> (Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a) -> (Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) a)
Case conversion may be inaccurate. Consider using '#align max_eq_left_of_lt max_eq_left_of_ltₓ'. -/
theorem max_eq_left_of_lt {a b : α} (h : b < a) : max a b = a :=
  max_eq_left (le_of_lt h)
#align max_eq_left_of_lt max_eq_left_of_lt

/- warning: max_eq_right_of_lt -> max_eq_right_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) b)
Case conversion may be inaccurate. Consider using '#align max_eq_right_of_lt max_eq_right_of_ltₓ'. -/
theorem max_eq_right_of_lt {a b : α} (h : a < b) : max a b = b :=
  max_eq_right (le_of_lt h)
#align max_eq_right_of_lt max_eq_right_of_lt

/- warning: lt_min -> lt_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a (LinearOrder.min.{u1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align lt_min lt_minₓ'. -/
-- these use the fact that it is a linear ordering
theorem lt_min {a b c : α} (h₁ : a < b) (h₂ : a < c) : a < min b c :=
  Or.elim (le_or_gt b c) (fun h : b ≤ c => minTac.1 b c) fun h : b > c => minTac.1 b c
#align lt_min lt_min

/- warning: max_lt -> max_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) (LinearOrder.max.{u1} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) c)
Case conversion may be inaccurate. Consider using '#align max_lt max_ltₓ'. -/
theorem max_lt {a b c : α} (h₁ : a < c) (h₂ : b < c) : max a b < c :=
  Or.elim (le_or_gt a b) (fun h : a ≤ b => minTac.1 b a) fun h : a > b => minTac.1 a b
#align max_lt max_lt

end

