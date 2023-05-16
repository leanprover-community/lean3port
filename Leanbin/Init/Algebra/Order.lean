/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.algebra.order
! leanprover-community/lean commit c2bcdbcbe741ed37c361a30d38e179182b989f76
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Classical
import Leanbin.Init.Meta.Name
import Leanbin.Init.Algebra.Classes

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option default_priority -/
/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

universe u

variable {α : Type u}

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option auto_param.check_exists -/
set_option auto_param.check_exists false

section Preorder

/-!
### Definition of `preorder` and lemmas about types with a `preorder`
-/


#print Preorder /-
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic order_laws_tac -/
/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by
    run_tac
      order_laws_tac
#align preorder Preorder
-/

variable [Preorder α]

/- warning: le_refl -> le_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a a
Case conversion may be inaccurate. Consider using '#align le_refl le_reflₓ'. -/
/-- The relation `≤` on a preorder is reflexive. -/
@[refl]
theorem le_refl : ∀ a : α, a ≤ a :=
  Preorder.le_refl
#align le_refl le_refl

/- warning: le_trans -> le_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) b c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align le_trans le_transₓ'. -/
/-- The relation `≤` on a preorder is transitive. -/
@[trans]
theorem le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
  Preorder.le_trans
#align le_trans le_trans

/- warning: lt_iff_le_not_le -> lt_iff_le_not_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) (And (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b) (Not (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) (And (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) (Not (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a)))
Case conversion may be inaccurate. Consider using '#align lt_iff_le_not_le lt_iff_le_not_leₓ'. -/
theorem lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  Preorder.lt_iff_le_not_le
#align lt_iff_le_not_le lt_iff_le_not_le

/- warning: lt_of_le_not_le -> lt_of_le_not_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b) -> (Not (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) b a)) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (Not (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align lt_of_le_not_le lt_of_le_not_leₓ'. -/
theorem lt_of_le_not_le : ∀ {a b : α}, a ≤ b → ¬b ≤ a → a < b
  | a, b, hab, hba => lt_iff_le_not_le.mpr ⟨hab, hba⟩
#align lt_of_le_not_le lt_of_le_not_le

/- warning: le_not_le_of_lt -> le_not_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (And (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b) (Not (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (And (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) (Not (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a)))
Case conversion may be inaccurate. Consider using '#align le_not_le_of_lt le_not_le_of_ltₓ'. -/
theorem le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬b ≤ a
  | a, b, hab => lt_iff_le_not_le.mp hab
#align le_not_le_of_lt le_not_le_of_lt

/- warning: le_of_eq -> le_of_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α a b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align le_of_eq le_of_eqₓ'. -/
theorem le_of_eq {a b : α} : a = b → a ≤ b := fun h => h ▸ le_refl a
#align le_of_eq le_of_eq

/- warning: ge_trans -> ge_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b) -> (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1) b c) -> (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) b c) -> (GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align ge_trans ge_transₓ'. -/
@[trans]
theorem ge_trans : ∀ {a b c : α}, a ≥ b → b ≥ c → a ≥ c := fun a b c h₁ h₂ => le_trans h₂ h₁
#align ge_trans ge_trans

/- warning: lt_irrefl -> lt_irrefl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Not (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Not (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a a)
Case conversion may be inaccurate. Consider using '#align lt_irrefl lt_irreflₓ'. -/
theorem lt_irrefl : ∀ a : α, ¬a < a
  | a, haa =>
    match le_not_le_of_lt haa with
    | ⟨h1, h2⟩ => False.ndrec _ (h2 h1)
#align lt_irrefl lt_irrefl

/- warning: gt_irrefl -> gt_irrefl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Not (GT.gt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Not (GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1) a a)
Case conversion may be inaccurate. Consider using '#align gt_irrefl gt_irreflₓ'. -/
theorem gt_irrefl : ∀ a : α, ¬a > a :=
  lt_irrefl
#align gt_irrefl gt_irrefl

/- warning: lt_trans -> lt_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align lt_trans lt_transₓ'. -/
@[trans]
theorem lt_trans : ∀ {a b c : α}, a < b → b < c → a < c
  | a, b, c, hab, hbc =>
    match le_not_le_of_lt hab, le_not_le_of_lt hbc with
    | ⟨hab, hba⟩, ⟨hbc, hcb⟩ => lt_of_le_not_le (le_trans hab hbc) fun hca => hcb (le_trans hca hab)
#align lt_trans lt_trans

/- warning: gt_trans -> gt_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (GT.gt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (GT.gt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) b c) -> (GT.gt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1) b c) -> (GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align gt_trans gt_transₓ'. -/
@[trans]
theorem gt_trans : ∀ {a b c : α}, a > b → b > c → a > c := fun a b c h₁ h₂ => lt_trans h₂ h₁
#align gt_trans gt_trans

/- warning: ne_of_lt -> ne_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Ne.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Ne.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align ne_of_lt ne_of_ltₓ'. -/
theorem ne_of_lt {a b : α} (h : a < b) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
#align ne_of_lt ne_of_lt

/- warning: ne_of_gt -> ne_of_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) b a) -> (Ne.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) b a) -> (Ne.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align ne_of_gt ne_of_gtₓ'. -/
theorem ne_of_gt {a b : α} (h : b < a) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
#align ne_of_gt ne_of_gt

/- warning: lt_asymm -> lt_asymm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Not (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Not (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) b a))
Case conversion may be inaccurate. Consider using '#align lt_asymm lt_asymmₓ'. -/
theorem lt_asymm {a b : α} (h : a < b) : ¬b < a := fun h1 : b < a => lt_irrefl a (lt_trans h h1)
#align lt_asymm lt_asymm

/- warning: le_of_lt -> le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align le_of_lt le_of_ltₓ'. -/
theorem le_of_lt : ∀ {a b : α}, a < b → a ≤ b
  | a, b, hab => (le_not_le_of_lt hab).left
#align le_of_lt le_of_lt

/- warning: lt_of_lt_of_le -> lt_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_of_le lt_of_lt_of_leₓ'. -/
@[trans]
theorem lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c
  | a, b, c, hab, hbc =>
    let ⟨hab, hba⟩ := le_not_le_of_lt hab
    lt_of_le_not_le (le_trans hab hbc) fun hca => hba (le_trans hbc hca)
#align lt_of_lt_of_le lt_of_lt_of_le

/- warning: lt_of_le_of_lt -> lt_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_le_of_lt lt_of_le_of_ltₓ'. -/
@[trans]
theorem lt_of_le_of_lt : ∀ {a b c : α}, a ≤ b → b < c → a < c
  | a, b, c, hab, hbc =>
    let ⟨hbc, hcb⟩ := le_not_le_of_lt hbc
    lt_of_le_not_le (le_trans hab hbc) fun hca => hcb (le_trans hca hab)
#align lt_of_le_of_lt lt_of_le_of_lt

/- warning: gt_of_gt_of_ge -> gt_of_gt_of_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (GT.gt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1) b c) -> (GT.gt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) b c) -> (GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align gt_of_gt_of_ge gt_of_gt_of_geₓ'. -/
@[trans]
theorem gt_of_gt_of_ge {a b c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
  lt_of_le_of_lt h₂ h₁
#align gt_of_gt_of_ge gt_of_gt_of_ge

/- warning: gt_of_ge_of_gt -> gt_of_ge_of_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b) -> (GT.gt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) b c) -> (GT.gt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α} {c : α}, (GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1) b c) -> (GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align gt_of_ge_of_gt gt_of_ge_of_gtₓ'. -/
@[trans]
theorem gt_of_ge_of_gt {a b c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
  lt_of_lt_of_le h₂ h₁
#align gt_of_ge_of_gt gt_of_ge_of_gt

/- warning: not_le_of_gt -> not_le_of_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (GT.gt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Not (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (GT.gt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Not (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align not_le_of_gt not_le_of_gtₓ'. -/
theorem not_le_of_gt {a b : α} (h : a > b) : ¬a ≤ b :=
  (le_not_le_of_lt h).right
#align not_le_of_gt not_le_of_gt

/- warning: not_lt_of_ge -> not_lt_of_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b) -> (Not (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (Not (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align not_lt_of_ge not_lt_of_geₓ'. -/
theorem not_lt_of_ge {a b : α} (h : a ≥ b) : ¬a < b := fun hab => not_le_of_gt hab h
#align not_lt_of_ge not_lt_of_ge

/- warning: le_of_lt_or_eq -> le_of_lt_or_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (Or (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) (Eq.{succ u1} α a b)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (Or (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) (Eq.{succ u1} α a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align le_of_lt_or_eq le_of_lt_or_eqₓ'. -/
theorem le_of_lt_or_eq : ∀ {a b : α}, a < b ∨ a = b → a ≤ b
  | a, b, Or.inl hab => le_of_lt hab
  | a, b, Or.inr hab => hab ▸ le_refl _
#align le_of_lt_or_eq le_of_lt_or_eq

/- warning: le_of_eq_or_lt -> le_of_eq_or_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (Or (Eq.{succ u1} α a b) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, (Or (Eq.{succ u1} α a b) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align le_of_eq_or_lt le_of_eq_or_ltₓ'. -/
theorem le_of_eq_or_lt {a b : α} (h : a = b ∨ a < b) : a ≤ b :=
  Or.elim h le_of_eq le_of_lt
#align le_of_eq_or_lt le_of_eq_or_lt

/- warning: decidable_lt_of_decidable_le -> decidableLTOfDecidableLE is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1))], DecidableRel.{succ u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Init.Algebra.Order._hyg.1583 : α) (x._@.Mathlib.Init.Algebra.Order._hyg.1585 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Init.Algebra.Order._hyg.1583 x._@.Mathlib.Init.Algebra.Order._hyg.1585)], DecidableRel.{succ u1} α (fun (x._@.Mathlib.Init.Algebra.Order._hyg.1600 : α) (x._@.Mathlib.Init.Algebra.Order._hyg.1602 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) x._@.Mathlib.Init.Algebra.Order._hyg.1600 x._@.Mathlib.Init.Algebra.Order._hyg.1602)
Case conversion may be inaccurate. Consider using '#align decidable_lt_of_decidable_le decidableLTOfDecidableLEₓ'. -/
/-- `<` is decidable if `≤` is. -/
def decidableLTOfDecidableLE [@DecidableRel α (· ≤ ·)] : @DecidableRel α (· < ·)
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isFalse fun hab' => not_le_of_gt hab' hba
      else isTrue <| lt_of_le_not_le hab hba
    else isFalse fun hab' => hab (le_of_lt hab')
#align decidable_lt_of_decidable_le decidableLTOfDecidableLE

end Preorder

section PartialOrder

/-!
### Definition of `partial_order` and lemmas about types with a partial order
-/


#print PartialOrder /-
/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
#align partial_order PartialOrder
-/

variable [PartialOrder α]

/- warning: le_antisymm -> le_antisymm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b a) -> (Eq.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b a) -> (Eq.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align le_antisymm le_antisymmₓ'. -/
theorem le_antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
  PartialOrder.le_antisymm
#align le_antisymm le_antisymm

/- warning: le_antisymm_iff -> le_antisymm_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α a b) (And (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α a b) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b a))
Case conversion may be inaccurate. Consider using '#align le_antisymm_iff le_antisymm_iffₓ'. -/
theorem le_antisymm_iff {a b : α} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩
#align le_antisymm_iff le_antisymm_iff

/- warning: lt_of_le_of_ne -> lt_of_le_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (Ne.{succ u1} α a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (Ne.{succ u1} α a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align lt_of_le_of_ne lt_of_le_of_neₓ'. -/
theorem lt_of_le_of_ne {a b : α} : a ≤ b → a ≠ b → a < b := fun h₁ h₂ =>
  lt_of_le_not_le h₁ <| mt (le_antisymm h₁) h₂
#align lt_of_le_of_ne lt_of_le_of_ne

/- warning: decidable_eq_of_decidable_le -> decidableEqOfDecidableLE is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))], DecidableEq.{succ u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Init.Algebra.Order._hyg.1891 : α) (x._@.Mathlib.Init.Algebra.Order._hyg.1893 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Init.Algebra.Order._hyg.1891 x._@.Mathlib.Init.Algebra.Order._hyg.1893)], DecidableEq.{succ u1} α
Case conversion may be inaccurate. Consider using '#align decidable_eq_of_decidable_le decidableEqOfDecidableLEₓ'. -/
/-- Equality is decidable if `≤` is. -/
def decidableEqOfDecidableLE [@DecidableRel α (· ≤ ·)] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isTrue (le_antisymm hab hba) else isFalse fun heq => hba (HEq ▸ le_refl _)
    else isFalse fun heq => hab (HEq ▸ le_refl _)
#align decidable_eq_of_decidable_le decidableEqOfDecidableLE

namespace Decidable

variable [@DecidableRel α (· ≤ ·)]

/- warning: decidable.lt_or_eq_of_le -> Decidable.lt_or_eq_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (Or (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Eq.{succ u1} α a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Init.Algebra.Order._hyg.2046 : α) (x._@.Mathlib.Init.Algebra.Order._hyg.2048 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Init.Algebra.Order._hyg.2046 x._@.Mathlib.Init.Algebra.Order._hyg.2048)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Eq.{succ u1} α a b))
Case conversion may be inaccurate. Consider using '#align decidable.lt_or_eq_of_le Decidable.lt_or_eq_of_leₓ'. -/
theorem lt_or_eq_of_le {a b : α} (hab : a ≤ b) : a < b ∨ a = b :=
  if hba : b ≤ a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_le hab hba)
#align decidable.lt_or_eq_of_le Decidable.lt_or_eq_of_le

/- warning: decidable.eq_or_lt_of_le -> Decidable.eq_or_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (Or (Eq.{succ u1} α a b) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Init.Algebra.Order._hyg.2123 : α) (x._@.Mathlib.Init.Algebra.Order._hyg.2125 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Init.Algebra.Order._hyg.2123 x._@.Mathlib.Init.Algebra.Order._hyg.2125)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (Or (Eq.{succ u1} α a b) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align decidable.eq_or_lt_of_le Decidable.eq_or_lt_of_leₓ'. -/
theorem eq_or_lt_of_le {a b : α} (hab : a ≤ b) : a = b ∨ a < b :=
  (lt_or_eq_of_le hab).symm
#align decidable.eq_or_lt_of_le Decidable.eq_or_lt_of_le

/- warning: decidable.le_iff_lt_or_eq -> Decidable.le_iff_lt_or_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Or (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Eq.{succ u1} α a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Init.Algebra.Order._hyg.2172 : α) (x._@.Mathlib.Init.Algebra.Order._hyg.2174 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Init.Algebra.Order._hyg.2172 x._@.Mathlib.Init.Algebra.Order._hyg.2174)] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Eq.{succ u1} α a b))
Case conversion may be inaccurate. Consider using '#align decidable.le_iff_lt_or_eq Decidable.le_iff_lt_or_eqₓ'. -/
theorem le_iff_lt_or_eq {a b : α} : a ≤ b ↔ a < b ∨ a = b :=
  ⟨lt_or_eq_of_le, le_of_lt_or_eq⟩
#align decidable.le_iff_lt_or_eq Decidable.le_iff_lt_or_eq

end Decidable

attribute [local instance] Classical.propDecidable

/- warning: lt_or_eq_of_le -> lt_or_eq_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (Or (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Eq.{succ u1} α a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Eq.{succ u1} α a b))
Case conversion may be inaccurate. Consider using '#align lt_or_eq_of_le lt_or_eq_of_leₓ'. -/
theorem lt_or_eq_of_le {a b : α} : a ≤ b → a < b ∨ a = b :=
  Decidable.lt_or_eq_of_le
#align lt_or_eq_of_le lt_or_eq_of_le

/- warning: le_iff_lt_or_eq -> le_iff_lt_or_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Or (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Eq.{succ u1} α a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) (Eq.{succ u1} α a b))
Case conversion may be inaccurate. Consider using '#align le_iff_lt_or_eq le_iff_lt_or_eqₓ'. -/
theorem le_iff_lt_or_eq {a b : α} : a ≤ b ↔ a < b ∨ a = b :=
  Decidable.le_iff_lt_or_eq
#align le_iff_lt_or_eq le_iff_lt_or_eq

end PartialOrder

section LinearOrder

/-!
### Definition of `linear_order` and lemmas about types with a linear order
-/


#print maxDefault /-
/-- Default definition of `max`. -/
def maxDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if a ≤ b then b else a
#align max_default maxDefault
-/

#print minDefault /-
/-- Default definition of `min`. -/
def minDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if a ≤ b then a else b
#align min_default minDefault
-/

#print LinearOrder /-
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.interactive.reflexivity -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.interactive.reflexivity -/
/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`. -/
class LinearOrder (α : Type u) extends PartialOrder α where
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
  decidableLe : DecidableRel (· ≤ ·)
  DecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ decidable_le
  decidableLt : DecidableRel ((· < ·) : α → α → Prop) := @decidableLTOfDecidableLE _ _ decidable_le
  max : α → α → α := @maxDefault α _ _
  max_def : max = @maxDefault α _ decidable_le := by
    run_tac
      tactic.interactive.reflexivity
  min : α → α → α := @minDefault α _ _
  min_def : min = @minDefault α _ decidable_le := by
    run_tac
      tactic.interactive.reflexivity
#align linear_order LinearOrder
-/

variable [LinearOrder α]

attribute [local instance] LinearOrder.decidableLe

/- warning: le_total -> le_total is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align le_total le_totalₓ'. -/
theorem le_total : ∀ a b : α, a ≤ b ∨ b ≤ a :=
  LinearOrder.le_total
#align le_total le_total

/- warning: le_of_not_ge -> le_of_not_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align le_of_not_ge le_of_not_geₓ'. -/
theorem le_of_not_ge {a b : α} : ¬a ≥ b → a ≤ b :=
  Or.resolve_left (le_total b a)
#align le_of_not_ge le_of_not_ge

/- warning: le_of_not_le -> le_of_not_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align le_of_not_le le_of_not_leₓ'. -/
theorem le_of_not_le {a b : α} : ¬a ≤ b → b ≤ a :=
  Or.resolve_left (le_total a b)
#align le_of_not_le le_of_not_le

/- warning: not_lt_of_gt -> not_lt_of_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (GT.gt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (Not (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) -> (Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align not_lt_of_gt not_lt_of_gtₓ'. -/
theorem not_lt_of_gt {a b : α} (h : a > b) : ¬a < b :=
  lt_asymm h
#align not_lt_of_gt not_lt_of_gt

/- warning: lt_trichotomy -> lt_trichotomy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (Or (Eq.{succ u1} α a b) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (Or (Eq.{succ u1} α a b) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a))
Case conversion may be inaccurate. Consider using '#align lt_trichotomy lt_trichotomyₓ'. -/
theorem lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a :=
  Or.elim (le_total a b)
    (fun h : a ≤ b =>
      Or.elim (Decidable.lt_or_eq_of_le h) (fun h : a < b => Or.inl h) fun h : a = b =>
        Or.inr (Or.inl h))
    fun h : b ≤ a =>
    Or.elim (Decidable.lt_or_eq_of_le h) (fun h : b < a => Or.inr (Or.inr h)) fun h : b = a =>
      Or.inr (Or.inl h.symm)
#align lt_trichotomy lt_trichotomy

/- warning: le_of_not_lt -> le_of_not_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align le_of_not_lt le_of_not_ltₓ'. -/
theorem le_of_not_lt {a b : α} (h : ¬b < a) : a ≤ b :=
  match lt_trichotomy a b with
  | Or.inl hlt => le_of_lt hlt
  | Or.inr (Or.inl HEq) => HEq ▸ le_refl a
  | Or.inr (Or.inr hgt) => absurd hgt h
#align le_of_not_lt le_of_not_lt

/- warning: le_of_not_gt -> le_of_not_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (GT.gt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align le_of_not_gt le_of_not_gtₓ'. -/
theorem le_of_not_gt {a b : α} : ¬a > b → a ≤ b :=
  le_of_not_lt
#align le_of_not_gt le_of_not_gt

/- warning: lt_of_not_ge -> lt_of_not_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align lt_of_not_ge lt_of_not_geₓ'. -/
theorem lt_of_not_ge {a b : α} (h : ¬a ≥ b) : a < b :=
  lt_of_le_not_le ((le_total _ _).resolve_right h) h
#align lt_of_not_ge lt_of_not_ge

/- warning: lt_or_le -> lt_or_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align lt_or_le lt_or_leₓ'. -/
theorem lt_or_le (a b : α) : a < b ∨ b ≤ a :=
  if hba : b ≤ a then Or.inr hba else Or.inl <| lt_of_not_ge hba
#align lt_or_le lt_or_le

/- warning: le_or_lt -> le_or_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align le_or_lt le_or_ltₓ'. -/
theorem le_or_lt (a b : α) : a ≤ b ∨ b < a :=
  (lt_or_le b a).symm
#align le_or_lt le_or_lt

/- warning: lt_or_ge -> lt_or_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align lt_or_ge lt_or_geₓ'. -/
theorem lt_or_ge : ∀ a b : α, a < b ∨ a ≥ b :=
  lt_or_le
#align lt_or_ge lt_or_ge

/- warning: le_or_gt -> le_or_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (GT.gt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (b : α), Or (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align le_or_gt le_or_gtₓ'. -/
theorem le_or_gt : ∀ a b : α, a ≤ b ∨ a > b :=
  le_or_lt
#align le_or_gt le_or_gt

/- warning: lt_or_gt_of_ne -> lt_or_gt_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Ne.{succ u1} α a b) -> (Or (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (GT.gt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Ne.{succ u1} α a b) -> (Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align lt_or_gt_of_ne lt_or_gt_of_neₓ'. -/
theorem lt_or_gt_of_ne {a b : α} (h : a ≠ b) : a < b ∨ a > b :=
  match lt_trichotomy a b with
  | Or.inl hlt => Or.inl hlt
  | Or.inr (Or.inl HEq) => absurd HEq h
  | Or.inr (Or.inr hgt) => Or.inr hgt
#align lt_or_gt_of_ne lt_or_gt_of_ne

/- warning: ne_iff_lt_or_gt -> ne_iff_lt_or_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Iff (Ne.{succ u1} α a b) (Or (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (GT.gt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Iff (Ne.{succ u1} α a b) (Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b) (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align ne_iff_lt_or_gt ne_iff_lt_or_gtₓ'. -/
theorem ne_iff_lt_or_gt {a b : α} : a ≠ b ↔ a < b ∨ a > b :=
  ⟨lt_or_gt_of_ne, fun o => Or.elim o ne_of_lt ne_of_gt⟩
#align ne_iff_lt_or_gt ne_iff_lt_or_gt

/- warning: lt_iff_not_ge -> lt_iff_not_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (x : α) (y : α), Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) x y) (Not (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (x : α) (y : α), Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) x y) (Not (GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) x y))
Case conversion may be inaccurate. Consider using '#align lt_iff_not_ge lt_iff_not_geₓ'. -/
theorem lt_iff_not_ge (x y : α) : x < y ↔ ¬x ≥ y :=
  ⟨not_le_of_gt, lt_of_not_ge⟩
#align lt_iff_not_ge lt_iff_not_ge

/- warning: not_lt -> not_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Iff (Not (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Iff (Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align not_lt not_ltₓ'. -/
@[simp]
theorem not_lt {a b : α} : ¬a < b ↔ b ≤ a :=
  ⟨le_of_not_gt, not_lt_of_ge⟩
#align not_lt not_lt

/- warning: not_le -> not_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Iff (Not (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, Iff (Not (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align not_le not_leₓ'. -/
@[simp]
theorem not_le {a b : α} : ¬a ≤ b ↔ b < a :=
  (lt_iff_not_ge _ _).symm
#align not_le not_le

instance (a b : α) : Decidable (a < b) :=
  LinearOrder.decidableLt a b

instance (a b : α) : Decidable (a ≤ b) :=
  LinearOrder.decidableLe a b

instance (a b : α) : Decidable (a = b) :=
  LinearOrder.decidableEq a b

/- warning: eq_or_lt_of_not_lt -> eq_or_lt_of_not_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) -> (Or (Eq.{succ u1} α a b) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α}, (Not (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) a b)) -> (Or (Eq.{succ u1} α a b) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) b a))
Case conversion may be inaccurate. Consider using '#align eq_or_lt_of_not_lt eq_or_lt_of_not_ltₓ'. -/
theorem eq_or_lt_of_not_lt {a b : α} (h : ¬a < b) : a = b ∨ b < a :=
  if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_ge fun hge => h (lt_of_le_of_ne hge h₁))
#align eq_or_lt_of_not_lt eq_or_lt_of_not_lt

instance : IsTotalPreorder α (· ≤ ·)
    where
  trans := @le_trans _ _
  Total := le_total

/- warning: is_strict_weak_order_of_linear_order -> isStrictWeakOrder_of_linearOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α], IsStrictWeakOrder.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α], IsStrictWeakOrder.{u1} α (fun (x._@.Mathlib.Init.Algebra.Order._hyg.4090 : α) (x._@.Mathlib.Init.Algebra.Order._hyg.4092 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Init.Algebra.Order._hyg.4090 x._@.Mathlib.Init.Algebra.Order._hyg.4092)
Case conversion may be inaccurate. Consider using '#align is_strict_weak_order_of_linear_order isStrictWeakOrder_of_linearOrderₓ'. -/
-- TODO(Leo): decide whether we should keep this instance or not
instance isStrictWeakOrder_of_linearOrder : IsStrictWeakOrder α (· < ·) :=
  isStrictWeakOrder_of_isTotalPreorder lt_iff_not_ge
#align is_strict_weak_order_of_linear_order isStrictWeakOrder_of_linearOrder

/- warning: is_strict_total_order_of_linear_order -> isStrictTotalOrder_of_linearOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α], IsStrictTotalOrder.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α], IsStrictTotalOrder.{u1} α (fun (x._@.Mathlib.Init.Algebra.Order._hyg.4143 : α) (x._@.Mathlib.Init.Algebra.Order._hyg.4145 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Init.Algebra.Order._hyg.4143 x._@.Mathlib.Init.Algebra.Order._hyg.4145)
Case conversion may be inaccurate. Consider using '#align is_strict_total_order_of_linear_order isStrictTotalOrder_of_linearOrderₓ'. -/
-- TODO(Leo): decide whether we should keep this instance or not
instance isStrictTotalOrder_of_linearOrder : IsStrictTotalOrder α (· < ·)
    where trichotomous := lt_trichotomy
#align is_strict_total_order_of_linear_order isStrictTotalOrder_of_linearOrder

/- warning: lt_by_cases -> ltByCases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (x : α) (y : α) {P : Sort.{u2}}, ((LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) x y) -> P) -> ((Eq.{succ u1} α x y) -> P) -> ((LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) y x) -> P) -> P
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (x : α) (y : α) {P : Sort.{u2}}, ((LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) x y) -> P) -> ((Eq.{succ u1} α x y) -> P) -> ((LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_1))) y x) -> P) -> P
Case conversion may be inaccurate. Consider using '#align lt_by_cases ltByCasesₓ'. -/
/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
def ltByCases (x y : α) {P : Sort _} (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
  if h : x < y then h₁ h
  else if h' : y < x then h₃ h' else h₂ (le_antisymm (le_of_not_gt h') (le_of_not_gt h))
#align lt_by_cases ltByCases

/- warning: le_imp_le_of_lt_imp_lt -> le_imp_le_of_lt_imp_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u1} α] [_inst_3 : LinearOrder.{u2} β] {a : α} {b : α} {c : β} {d : β}, ((LT.lt.{u2} β (Preorder.toHasLt.{u2} β (PartialOrder.toPreorder.{u2} β (LinearOrder.toPartialOrder.{u2} β _inst_3))) d c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b a)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a b) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (LinearOrder.toPartialOrder.{u2} β _inst_3))) c d)
but is expected to have type
  forall {α : Type.{u2}} {_inst_1 : Type.{u1}} [β : Preorder.{u2} α] [_inst_2 : LinearOrder.{u1} _inst_1] {_inst_3 : α} {a : α} {b : _inst_1} {c : _inst_1}, ((LT.lt.{u1} _inst_1 (Preorder.toLT.{u1} _inst_1 (PartialOrder.toPreorder.{u1} _inst_1 (LinearOrder.toPartialOrder.{u1} _inst_1 _inst_2))) c b) -> (LT.lt.{u2} α (Preorder.toLT.{u2} α β) a _inst_3)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α β) _inst_3 a) -> (LE.le.{u1} _inst_1 (Preorder.toLE.{u1} _inst_1 (PartialOrder.toPreorder.{u1} _inst_1 (LinearOrder.toPartialOrder.{u1} _inst_1 _inst_2))) b c)
Case conversion may be inaccurate. Consider using '#align le_imp_le_of_lt_imp_lt le_imp_le_of_lt_imp_ltₓ'. -/
theorem le_imp_le_of_lt_imp_lt {β} [Preorder α] [LinearOrder β] {a b : α} {c d : β}
    (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
  le_of_not_lt fun h' => not_le_of_gt (H h') h
#align le_imp_le_of_lt_imp_lt le_imp_le_of_lt_imp_lt

end LinearOrder

