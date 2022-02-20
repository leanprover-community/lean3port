/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Bool.Basic
import Leanbin.Init.Meta.Default

attribute [simp] cond bor band bnot bxor

@[simp]
theorem cond_a_a.{u} {α : Type u} (b : Bool) (a : α) : cond b a a = a := by
  cases b <;> simp

@[simp]
theorem band_self (b : Bool) : (b && b) = b := by
  cases b <;> simp

@[simp]
theorem band_tt (b : Bool) : (b && tt) = b := by
  cases b <;> simp

@[simp]
theorem band_ff (b : Bool) : (b && ff) = ff := by
  cases b <;> simp

@[simp]
theorem tt_band (b : Bool) : (tt && b) = b := by
  cases b <;> simp

@[simp]
theorem ff_band (b : Bool) : (ff && b) = ff := by
  cases b <;> simp

@[simp]
theorem bor_self (b : Bool) : (b || b) = b := by
  cases b <;> simp

@[simp]
theorem bor_tt (b : Bool) : (b || tt) = tt := by
  cases b <;> simp

@[simp]
theorem bor_ff (b : Bool) : (b || ff) = b := by
  cases b <;> simp

@[simp]
theorem tt_bor (b : Bool) : (tt || b) = tt := by
  cases b <;> simp

@[simp]
theorem ff_bor (b : Bool) : (ff || b) = b := by
  cases b <;> simp

@[simp]
theorem bxor_self (b : Bool) : bxor b b = ff := by
  cases b <;> simp

@[simp]
theorem bxor_tt (b : Bool) : bxor b true = bnot b := by
  cases b <;> simp

theorem bxor_ff (b : Bool) : bxor b false = b := by
  cases b <;> simp

@[simp]
theorem tt_bxor (b : Bool) : bxor true b = bnot b := by
  cases b <;> simp

theorem ff_bxor (b : Bool) : bxor false b = b := by
  cases b <;> simp

@[simp]
theorem bnot_bnot (b : Bool) : bnot (bnot b) = b := by
  cases b <;> simp

theorem tt_eq_ff_eq_false : ¬tt = ff := by
  contradiction

theorem ff_eq_tt_eq_false : ¬ff = tt := by
  contradiction

@[simp]
theorem eq_ff_eq_not_eq_tt (b : Bool) : (¬b = tt) = (b = ff) := by
  cases b <;> simp

@[simp]
theorem eq_tt_eq_not_eq_ff (b : Bool) : (¬b = ff) = (b = tt) := by
  cases b <;> simp

theorem eq_ff_of_not_eq_tt {b : Bool} : ¬b = tt → b = ff :=
  Eq.mp (eq_ff_eq_not_eq_tt b)

theorem eq_tt_of_not_eq_ff {b : Bool} : ¬b = ff → b = tt :=
  Eq.mp (eq_tt_eq_not_eq_ff b)

@[simp]
theorem band_eq_true_eq_eq_tt_and_eq_tt (a b : Bool) : ((a && b) = tt) = (a = tt ∧ b = tt) := by
  cases a <;> cases b <;> simp

@[simp]
theorem bor_eq_true_eq_eq_tt_or_eq_tt (a b : Bool) : ((a || b) = tt) = (a = tt ∨ b = tt) := by
  cases a <;> cases b <;> simp

@[simp]
theorem bnot_eq_true_eq_eq_ff (a : Bool) : (bnot a = tt) = (a = ff) := by
  cases a <;> simp

@[simp]
theorem band_eq_false_eq_eq_ff_or_eq_ff (a b : Bool) : ((a && b) = ff) = (a = ff ∨ b = ff) := by
  cases a <;> cases b <;> simp

@[simp]
theorem bor_eq_false_eq_eq_ff_and_eq_ff (a b : Bool) : ((a || b) = ff) = (a = ff ∧ b = ff) := by
  cases a <;> cases b <;> simp

@[simp]
theorem bnot_eq_ff_eq_eq_tt (a : Bool) : (bnot a = ff) = (a = tt) := by
  cases a <;> simp

@[simp]
theorem coe_ff : ↑ff = False :=
  show (ff = tt) = False by
    simp

@[simp]
theorem coe_tt : ↑tt = True :=
  show (tt = tt) = True by
    simp

@[simp]
theorem coe_sort_ff : ↥ff = False :=
  show (ff = tt) = False by
    simp

@[simp]
theorem coe_sort_tt : ↥tt = True :=
  show (tt = tt) = True by
    simp

@[simp]
theorem to_bool_iff (p : Prop) [d : Decidable p] : toBool p = tt ↔ p :=
  match d with
  | is_true hp => ⟨fun h => hp, fun _ => rfl⟩
  | is_false hnp => ⟨fun h => Bool.noConfusion h, fun hp => absurd hp hnp⟩

theorem to_bool_true {p : Prop} [Decidable p] : p → toBool p :=
  (to_bool_iff p).2

theorem to_bool_tt {p : Prop} [Decidable p] : p → toBool p = tt :=
  to_bool_true

theorem of_to_bool_true {p : Prop} [Decidable p] : toBool p → p :=
  (to_bool_iff p).1

theorem bool_iff_false {b : Bool} : ¬b ↔ b = ff := by
  cases b <;>
    exact by
      decide

theorem bool_eq_false {b : Bool} : ¬b → b = ff :=
  bool_iff_false.1

@[simp]
theorem to_bool_ff_iff (p : Prop) [Decidable p] : toBool p = ff ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (to_bool_iff _))

theorem to_bool_ff {p : Prop} [Decidable p] : ¬p → toBool p = ff :=
  (to_bool_ff_iff p).2

theorem of_to_bool_ff {p : Prop} [Decidable p] : toBool p = ff → ¬p :=
  (to_bool_ff_iff p).1

theorem to_bool_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : toBool p = toBool q := by
  induction' h' : to_bool q with
  exact to_bool_ff (mt h.1 <| of_to_bool_ff h')
  exact to_bool_true (h.2 <| of_to_bool_true h')

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
theorem bxor_coe_iff (a b : Bool) : bxor a b ↔ Xorₓ a b := by
  cases a <;>
    cases b <;>
      exact by
        decide

@[simp]
theorem ite_eq_tt_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = tt) = if c then a = tt else b = tt := by
  by_cases' c <;> simp [*]

@[simp]
theorem ite_eq_ff_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = ff) = if c then a = ff else b = ff := by
  by_cases' c <;> simp [*]

