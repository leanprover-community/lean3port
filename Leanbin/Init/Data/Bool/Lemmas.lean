/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Bool.Basic
import Leanbin.Init.Meta.Default

@[simp]
theorem cond_a_a.{u} {α : Type u} (b : Bool) (a : α) : cond b a a = a := by
  cases b <;> simp

@[simp]
theorem band_self (b : Bool) : (b && b) = b := by
  cases b <;> simp

@[simp]
theorem band_tt (b : Bool) : (b && true) = b := by
  cases b <;> simp

@[simp]
theorem band_ff (b : Bool) : (b && false) = false := by
  cases b <;> simp

@[simp]
theorem tt_band (b : Bool) : (true && b) = b := by
  cases b <;> simp

@[simp]
theorem ff_band (b : Bool) : (false && b) = false := by
  cases b <;> simp

@[simp]
theorem bor_self (b : Bool) : (b || b) = b := by
  cases b <;> simp

@[simp]
theorem bor_tt (b : Bool) : (b || true) = true := by
  cases b <;> simp

@[simp]
theorem bor_ff (b : Bool) : (b || false) = b := by
  cases b <;> simp

@[simp]
theorem tt_bor (b : Bool) : (true || b) = true := by
  cases b <;> simp

@[simp]
theorem ff_bor (b : Bool) : (false || b) = b := by
  cases b <;> simp

@[simp]
theorem bxor_self (b : Bool) : bxor b b = false := by
  cases b <;> simp

@[simp]
theorem bxor_tt (b : Bool) : bxor b true = bnot b := by
  cases b <;> simp

@[simp]
theorem bxor_ff (b : Bool) : bxor b false = b := by
  cases b <;> simp

@[simp]
theorem tt_bxor (b : Bool) : bxor true b = bnot b := by
  cases b <;> simp

@[simp]
theorem ff_bxor (b : Bool) : bxor false b = b := by
  cases b <;> simp

@[simp]
theorem bnot_bnot (b : Bool) : bnot (bnot b) = b := by
  cases b <;> simp

macro_rules | `(tactic| contradiction) => `(tactic| intro; contradiction)

theorem tt_eq_ff_eq_false : ¬true = false := by
  contradiction

theorem ff_eq_tt_eq_false : ¬false = true := by
  contradiction

@[simp]
theorem eq_ff_eq_not_eq_tt (b : Bool) : (¬b = true) = (b = false) := by
  cases b <;> simp

@[simp]
theorem eq_tt_eq_not_eq_ff (b : Bool) : (¬b = false) = (b = true) := by
  cases b <;> simp

theorem eq_ff_of_not_eq_tt {b : Bool} : ¬b = true → b = false :=
  Eq.mp (eq_ff_eq_not_eq_tt b)

theorem eq_tt_of_not_eq_ff {b : Bool} : ¬b = false → b = true :=
  Eq.mp (eq_tt_eq_not_eq_ff b)

@[simp]
theorem band_eq_true_eq_eq_tt_and_eq_tt (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

@[simp]
theorem bor_eq_true_eq_eq_tt_or_eq_tt (a b : Bool) : ((a || b) = true) = (a = true ∨ b = true) := by
  cases a <;> cases b <;> simp

@[simp]
theorem bnot_eq_true_eq_eq_ff (a : Bool) : (bnot a = true) = (a = false) := by
  cases a <;> simp

@[simp]
theorem band_eq_false_eq_eq_ff_or_eq_ff (a b : Bool) : ((a && b) = false) = (a = false ∨ b = false) := by
  cases a <;> cases b <;> simp

@[simp]
theorem bor_eq_false_eq_eq_ff_and_eq_ff (a b : Bool) : ((a || b) = false) = (a = false ∧ b = false) := by
  cases a <;> cases b <;> simp

@[simp]
theorem bnot_eq_ff_eq_eq_tt (a : Bool) : (bnot a = false) = (a = true) := by
  cases a <;> simp

@[simp]
theorem coe_ff : ↑false = False :=
  show (false = true) = False by
    simp

@[simp]
theorem coe_tt : ↑true = True :=
  show (true = true) = True by
    simp

@[simp]
theorem coe_sort_ff : false = False :=
  show (false = true) = False by
    simp

@[simp]
theorem coe_sort_tt : true = True :=
  show (true = true) = True by
    simp

@[simp]
theorem to_bool_iff (p : Prop) [d : Decidable p] : toBool p = true ↔ p :=
  match d with
  | isTrue hp => ⟨fun h => hp, fun _ => rfl⟩
  | isFalse hnp => ⟨fun h => Bool.noConfusion h, fun hp => absurd hp hnp⟩

theorem to_bool_true {p : Prop} [Decidable p] : p → toBool p :=
  (to_bool_iff p).2

theorem to_bool_tt {p : Prop} [Decidable p] : p → toBool p = true :=
  to_bool_true

theorem of_to_bool_true {p : Prop} [Decidable p] : toBool p → p :=
  (to_bool_iff p).1

theorem bool_iff_false {b : Bool} : ¬b ↔ b = false := by
  cases b <;>
    exact by
      decide

theorem bool_eq_false {b : Bool} : ¬b → b = false :=
  bool_iff_false.1

@[simp]
theorem to_bool_ff_iff (p : Prop) [Decidable p] : toBool p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (to_bool_iff _))

theorem to_bool_ff {p : Prop} [Decidable p] : ¬p → toBool p = false :=
  (to_bool_ff_iff p).2

theorem of_to_bool_ff {p : Prop} [Decidable p] : toBool p = false → ¬p :=
  (to_bool_ff_iff p).1

theorem to_bool_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : toBool p = toBool q :=
  match h' : toBool q with
  | false => to_bool_ff (mt h.1 <| of_to_bool_ff h')
  | true => to_bool_true (h.2 <| of_to_bool_true h')

@[simp]
theorem bor_coe_iff (a b : Bool) : a || b ↔ a ∨ b := by
  cases a <;>
    cases b <;>
      exact by
        decide

@[simp]
theorem band_coe_iff (a b : Bool) : a && b ↔ a ∧ b := by
  cases a <;>
    cases b <;>
      exact by
        decide

@[simp]
theorem bxor_coe_iff (a b : Bool) : bxor a b ↔ xor a b := by
  cases a <;>
    cases b <;>
      exact by
        decide

@[simp]
theorem bxor_bnot : bxor a (!b) = !bxor a b := by
  cases a <;> cases b <;> rfl

@[simp]
theorem bnot_bxor : bxor (!a) b = !bxor a b := by
  cases a <;> cases b <;> rfl

@[simp]
theorem ite_eq_tt_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = true) = if c then a = true else b = true := by
  by_cases c <;> simp [*]

@[simp]
theorem ite_eq_ff_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = false) = if c then a = false else b = false := by
  by_cases c <;> simp [*]

