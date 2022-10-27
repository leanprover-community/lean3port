/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import Leanbin.Init.Algebra.Order
import Leanbin.Init.Meta.Default

universe u

export LinearOrder (min max)

section

open Decidable Tactic

variable {α : Type u} [LinearOrder α]

theorem min_def (a b : α) : min a b = if a ≤ b then a else b := by rw [congr_fun LinearOrder.min_def a, minDefault]

theorem max_def (a b : α) : max a b = if b ≤ a then a else b := by rw [congr_fun LinearOrder.max_def a, maxDefault]

/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def min_tac_step : tactic Unit :=
  solve1 <| (((intros >> sorry) >> try sorry) >> try sorry) >> try sorry

unsafe def tactic.interactive.min_tac (a b : interactive.parse lean.parser.pexpr) : tactic Unit :=
  andthen (interactive.by_cases (none, pquote.1 ((%%ₓa) ≤ %%ₓb))) min_tac_step

/- warning: min_le_left -> min_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) (LinearOrder.min.{u} α _inst_1 a b) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.15 : LinearOrder.{u} α] (a : α) (b : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.15))) (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.15))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.15 a b) a b) a
Case conversion may be inaccurate. Consider using '#align min_le_left min_le_leftₓ'. -/
theorem min_le_left (a b : α) : min a b ≤ a :=
  minTac.1 a b

/- warning: min_le_right -> min_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) (LinearOrder.min.{u} α _inst_1 a b) b
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.67 : LinearOrder.{u} α] (a : α) (b : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.67))) (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.67))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.67 a b) a b) b
Case conversion may be inaccurate. Consider using '#align min_le_right min_le_rightₓ'. -/
theorem min_le_right (a b : α) : min a b ≤ b :=
  minTac.1 a b

/- warning: le_min -> le_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) c a) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) c b) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) c (LinearOrder.min.{u} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.118 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.118))) c a) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.118))) c b) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.118))) c (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.118))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.118 a b) a b))
Case conversion may be inaccurate. Consider using '#align le_min le_minₓ'. -/
theorem le_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b :=
  minTac.1 a b

/- warning: le_max_left -> le_max_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a (LinearOrder.max.{u} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.182 : LinearOrder.{u} α] (a : α) (b : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.182))) a (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.182))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.182 a b) a b)
Case conversion may be inaccurate. Consider using '#align le_max_left le_max_leftₓ'. -/
theorem le_max_left (a b : α) : a ≤ max a b :=
  minTac.1 b a

/- warning: le_max_right -> le_max_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) b (LinearOrder.max.{u} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.234 : LinearOrder.{u} α] (a : α) (b : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.234))) b (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.234))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.234 a b) a b)
Case conversion may be inaccurate. Consider using '#align le_max_right le_max_rightₓ'. -/
theorem le_max_right (a b : α) : b ≤ max a b :=
  minTac.1 b a

/- warning: max_le -> max_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) b c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) (LinearOrder.max.{u} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.286 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.286))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.286))) b c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.286))) (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.286))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.286 a b) a b) c)
Case conversion may be inaccurate. Consider using '#align max_le max_leₓ'. -/
theorem max_le {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c :=
  minTac.1 b a

/- warning: eq_min -> eq_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) c a) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) c b) -> (forall {d : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) d a) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) d b) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) d c)) -> (Eq.{succ u} α c (LinearOrder.min.{u} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.350 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.350))) c a) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.350))) c b) -> (forall {d : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.350))) d a) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.350))) d b) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.350))) d c)) -> (Eq.{succ u} α c (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.350))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.350 a b) a b))
Case conversion may be inaccurate. Consider using '#align eq_min eq_minₓ'. -/
theorem eq_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀ {d}, d ≤ a → d ≤ b → d ≤ c) : c = min a b :=
  le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

/- warning: min_comm -> min_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α), Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) (LinearOrder.min.{u} α _inst_1 b a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.416 : LinearOrder.{u} α] (a : α) (b : α), Eq.{succ u} α (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.416))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.416 a b) a b) (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.416))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.416 a b) b a)
Case conversion may be inaccurate. Consider using '#align min_comm min_commₓ'. -/
theorem min_comm (a b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) fun c h₁ h₂ => le_min h₂ h₁

/- warning: min_assoc -> min_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 (LinearOrder.min.{u} α _inst_1 a b) c) (LinearOrder.min.{u} α _inst_1 a (LinearOrder.min.{u} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.456 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.456))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.456 a b) (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.456))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.456 a b) a b) c) (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.456))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.456 a b) a (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.456))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.456 a b) b c))
Case conversion may be inaccurate. Consider using '#align min_assoc min_assocₓ'. -/
theorem min_assoc (a b c : α) : min (min a b) c = min a (min b c) := by
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
    

/- warning: min_left_comm -> min_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a (LinearOrder.min.{u} α _inst_1 b c)) (LinearOrder.min.{u} α _inst_1 b (LinearOrder.min.{u} α _inst_1 a c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.580 : LinearOrder.{u} α], LeftCommutative.{u u} α α (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.580))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.580 a b))
Case conversion may be inaccurate. Consider using '#align min_left_comm min_left_commₓ'. -/
theorem min_left_comm : ∀ a b c : α, min a (min b c) = min b (min a c) :=
  left_comm (@min α _) (@min_comm α _) (@min_assoc α _)

/- warning: min_self -> min_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α), Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a a) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.601 : LinearOrder.{u} α] (a : α), Eq.{succ u} α (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.601))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.601 a b) a a) a
Case conversion may be inaccurate. Consider using '#align min_self min_selfₓ'. -/
@[simp]
theorem min_self (a : α) : min a a = a :=
  minTac.1 a a

/- warning: min_eq_left -> min_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a b) -> (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.620 : LinearOrder.{u} α] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.620))) a b) -> (Eq.{succ u} α (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.620))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.620 a b) a b) a)
Case conversion may be inaccurate. Consider using '#align min_eq_left min_eq_leftₓ'. -/
@[ematch]
theorem min_eq_left {a b : α} (h : a ≤ b) : min a b = a := by
  apply Eq.symm
  apply eq_min (le_refl _) h
  intros
  assumption

/- warning: min_eq_right -> min_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) b a) -> (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.657 : LinearOrder.{u} α] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.657))) b a) -> (Eq.{succ u} α (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.657))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.657 a b) a b) b)
Case conversion may be inaccurate. Consider using '#align min_eq_right min_eq_rightₓ'. -/
@[ematch]
theorem min_eq_right {a b : α} (h : b ≤ a) : min a b = b :=
  Eq.subst (min_comm b a) (min_eq_left h)

/- warning: eq_max -> eq_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) b c) -> (forall {d : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a d) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) b d) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) c d)) -> (Eq.{succ u} α c (LinearOrder.max.{u} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.713 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.713))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.713))) b c) -> (forall {d : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.713))) a d) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.713))) b d) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.713))) c d)) -> (Eq.{succ u} α c (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.713))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.713 a b) a b))
Case conversion may be inaccurate. Consider using '#align eq_max eq_maxₓ'. -/
theorem eq_max {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀ {d}, a ≤ d → b ≤ d → c ≤ d) : c = max a b :=
  le_antisymm (h₃ (le_max_left a b) (le_max_right a b)) (max_le h₁ h₂)

/- warning: max_comm -> max_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α), Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) (LinearOrder.max.{u} α _inst_1 b a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.779 : LinearOrder.{u} α] (a : α) (b : α), Eq.{succ u} α (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.779))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.779 a b) a b) (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.779))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.779 a b) b a)
Case conversion may be inaccurate. Consider using '#align max_comm max_commₓ'. -/
theorem max_comm (a b : α) : max a b = max b a :=
  eq_max (le_max_right a b) (le_max_left a b) fun c h₁ h₂ => max_le h₂ h₁

/- warning: max_assoc -> max_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 (LinearOrder.max.{u} α _inst_1 a b) c) (LinearOrder.max.{u} α _inst_1 a (LinearOrder.max.{u} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.819 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.819))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.819 a b) (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.819))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.819 a b) a b) c) (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.819))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.819 a b) a (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.819))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.819 a b) b c))
Case conversion may be inaccurate. Consider using '#align max_assoc max_assocₓ'. -/
theorem max_assoc (a b c : α) : max (max a b) c = max a (max b c) := by
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
    

/- warning: max_left_comm -> max_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a (LinearOrder.max.{u} α _inst_1 b c)) (LinearOrder.max.{u} α _inst_1 b (LinearOrder.max.{u} α _inst_1 a c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.947 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.947))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.947 a b) a (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.947))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.947 a b) b c)) (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.947))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.947 a b) b (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.947))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.947 a b) a c))
Case conversion may be inaccurate. Consider using '#align max_left_comm max_left_commₓ'. -/
theorem max_left_comm : ∀ a b c : α, max a (max b c) = max b (max a c) :=
  left_comm (@max α _) (@max_comm α _) (@max_assoc α _)

/- warning: max_self -> max_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α), Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a a) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.986 : LinearOrder.{u} α] (a : α), Eq.{succ u} α (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.986))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.986 a b) a a) a
Case conversion may be inaccurate. Consider using '#align max_self max_selfₓ'. -/
@[simp]
theorem max_self (a : α) : max a a = a :=
  minTac.1 a a

/- warning: max_eq_left -> max_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) b a) -> (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.1005 : LinearOrder.{u} α] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1005))) b a) -> (Eq.{succ u} α (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1005))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1005 a b) a b) a)
Case conversion may be inaccurate. Consider using '#align max_eq_left max_eq_leftₓ'. -/
theorem max_eq_left {a b : α} (h : b ≤ a) : max a b = a := by
  apply Eq.symm
  apply eq_max (le_refl _) h
  intros
  assumption

/- warning: max_eq_right -> max_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a b) -> (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.1042 : LinearOrder.{u} α] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1042))) a b) -> (Eq.{succ u} α (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1042))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1042 a b) a b) b)
Case conversion may be inaccurate. Consider using '#align max_eq_right max_eq_rightₓ'. -/
theorem max_eq_right {a b : α} (h : a ≤ b) : max a b = b :=
  Eq.subst (max_comm b a) (max_eq_left h)

/- warning: min_eq_left_of_lt -> min_eq_left_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a b) -> (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.1100 : LinearOrder.{u} α] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1100))) a b) -> (Eq.{succ u} α (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1100))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1100 a b) a b) a)
Case conversion may be inaccurate. Consider using '#align min_eq_left_of_lt min_eq_left_of_ltₓ'. -/
-- these rely on lt_of_lt
theorem min_eq_left_of_lt {a b : α} (h : a < b) : min a b = a :=
  min_eq_left (le_of_lt h)

/- warning: min_eq_right_of_lt -> min_eq_right_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) b a) -> (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.1126 : LinearOrder.{u} α] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1126))) b a) -> (Eq.{succ u} α (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1126))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1126 a b) a b) b)
Case conversion may be inaccurate. Consider using '#align min_eq_right_of_lt min_eq_right_of_ltₓ'. -/
theorem min_eq_right_of_lt {a b : α} (h : b < a) : min a b = b :=
  min_eq_right (le_of_lt h)

/- warning: max_eq_left_of_lt -> max_eq_left_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) b a) -> (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.1152 : LinearOrder.{u} α] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1152))) b a) -> (Eq.{succ u} α (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1152))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1152 a b) a b) a)
Case conversion may be inaccurate. Consider using '#align max_eq_left_of_lt max_eq_left_of_ltₓ'. -/
theorem max_eq_left_of_lt {a b : α} (h : b < a) : max a b = a :=
  max_eq_left (le_of_lt h)

/- warning: max_eq_right_of_lt -> max_eq_right_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a b) -> (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.1178 : LinearOrder.{u} α] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1178))) a b) -> (Eq.{succ u} α (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1178))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1178 a b) a b) b)
Case conversion may be inaccurate. Consider using '#align max_eq_right_of_lt max_eq_right_of_ltₓ'. -/
theorem max_eq_right_of_lt {a b : α} (h : a < b) : max a b = b :=
  max_eq_right (le_of_lt h)

/- warning: lt_min -> lt_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a b) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a (LinearOrder.min.{u} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.1204 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1204))) a b) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1204))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1204))) a (min.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1204))) (fun (a : α) (b : α) => instDecidableLeToLEToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1204 a b) b c))
Case conversion may be inaccurate. Consider using '#align lt_min lt_minₓ'. -/
-- these use the fact that it is a linear ordering
theorem lt_min {a b c : α} (h₁ : a < b) (h₂ : a < c) : a < min b c :=
  Or.elim (le_or_gt b c) (fun h : b ≤ c => minTac.1 b c) fun h : b > c => minTac.1 b c

/- warning: max_lt -> max_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) b c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α _inst_1))) (LinearOrder.max.{u} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Init.Algebra.Functions._hyg.1335 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1335))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1335))) b c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1335))) (max.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (LinearOrder.toPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1335))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u} α inst._@.Mathlib.Init.Algebra.Functions._hyg.1335 a b) a b) c)
Case conversion may be inaccurate. Consider using '#align max_lt max_ltₓ'. -/
theorem max_lt {a b c : α} (h₁ : a < c) (h₂ : b < c) : max a b < c :=
  Or.elim (le_or_gt a b) (fun h : a ≤ b => minTac.1 b a) fun h : a > b => minTac.1 b a

end

