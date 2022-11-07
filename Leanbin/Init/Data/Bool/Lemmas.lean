/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Bool.Basic
import Leanbin.Init.Meta.Default

attribute [simp] cond or and not xor

#print Bool.cond_self /-
@[simp]
theorem Bool.cond_self.{u} {α : Type u} (b : Bool) (a : α) : cond b a a = a := by cases b <;> simp
-/

#print Bool.and_self /-
@[simp]
theorem Bool.and_self (b : Bool) : (b && b) = b := by cases b <;> simp
-/

#print Bool.and_true /-
@[simp]
theorem Bool.and_true (b : Bool) : (b && tt) = b := by cases b <;> simp
-/

#print Bool.and_false /-
@[simp]
theorem Bool.and_false (b : Bool) : (b && ff) = ff := by cases b <;> simp
-/

#print Bool.true_and /-
@[simp]
theorem Bool.true_and (b : Bool) : (tt && b) = b := by cases b <;> simp
-/

#print Bool.false_and /-
@[simp]
theorem Bool.false_and (b : Bool) : (ff && b) = ff := by cases b <;> simp
-/

#print Bool.or_self /-
@[simp]
theorem Bool.or_self (b : Bool) : (b || b) = b := by cases b <;> simp
-/

#print Bool.or_true /-
@[simp]
theorem Bool.or_true (b : Bool) : (b || tt) = tt := by cases b <;> simp
-/

#print Bool.or_false /-
@[simp]
theorem Bool.or_false (b : Bool) : (b || ff) = b := by cases b <;> simp
-/

#print Bool.true_or /-
@[simp]
theorem Bool.true_or (b : Bool) : (tt || b) = tt := by cases b <;> simp
-/

#print Bool.false_or /-
@[simp]
theorem Bool.false_or (b : Bool) : (ff || b) = b := by cases b <;> simp
-/

#print Bool.xor_self /-
@[simp]
theorem Bool.xor_self (b : Bool) : xor b b = ff := by cases b <;> simp
-/

#print Bool.xor_true /-
@[simp]
theorem Bool.xor_true (b : Bool) : xor b true = not b := by cases b <;> simp
-/

#print Bool.xor_false /-
theorem Bool.xor_false (b : Bool) : xor b false = b := by cases b <;> simp
-/

#print Bool.true_xor /-
@[simp]
theorem Bool.true_xor (b : Bool) : xor true b = not b := by cases b <;> simp
-/

#print Bool.false_xor /-
theorem Bool.false_xor (b : Bool) : xor false b = b := by cases b <;> simp
-/

#print Bool.not_not /-
@[simp]
theorem Bool.not_not (b : Bool) : not (not b) = b := by cases b <;> simp
-/

#print Bool.true_eq_false_eq_False /-
theorem Bool.true_eq_false_eq_False : ¬tt = ff := by contradiction
-/

#print Bool.false_eq_true_eq_False /-
theorem Bool.false_eq_true_eq_False : ¬ff = tt := by contradiction
-/

#print Bool.eq_false_eq_not_eq_true /-
@[simp]
theorem Bool.eq_false_eq_not_eq_true (b : Bool) : (¬b = tt) = (b = ff) := by cases b <;> simp
-/

@[simp]
theorem eq_tt_eq_not_eq_ff (b : Bool) : (¬b = ff) = (b = tt) := by cases b <;> simp

#print Bool.eq_false_of_not_eq_true /-
theorem Bool.eq_false_of_not_eq_true {b : Bool} : ¬b = tt → b = ff :=
  Eq.mp (Bool.eq_false_eq_not_eq_true b)
-/

#print Bool.eq_true_of_not_eq_false /-
theorem Bool.eq_true_of_not_eq_false {b : Bool} : ¬b = ff → b = tt :=
  Eq.mp (eq_tt_eq_not_eq_ff b)
-/

#print Bool.and_eq_true_eq_eq_true_and_eq_true /-
@[simp]
theorem Bool.and_eq_true_eq_eq_true_and_eq_true (a b : Bool) : ((a && b) = tt) = (a = tt ∧ b = tt) := by
  cases a <;> cases b <;> simp
-/

#print Bool.or_eq_true_eq_eq_true_or_eq_true /-
@[simp]
theorem Bool.or_eq_true_eq_eq_true_or_eq_true (a b : Bool) : ((a || b) = tt) = (a = tt ∨ b = tt) := by
  cases a <;> cases b <;> simp
-/

#print Bool.not_eq_true_eq_eq_false /-
@[simp]
theorem Bool.not_eq_true_eq_eq_false (a : Bool) : (not a = tt) = (a = ff) := by cases a <;> simp
-/

#print Bool.and_eq_false_eq_eq_false_or_eq_false /-
@[simp]
theorem Bool.and_eq_false_eq_eq_false_or_eq_false (a b : Bool) : ((a && b) = ff) = (a = ff ∨ b = ff) := by
  cases a <;> cases b <;> simp
-/

#print Bool.or_eq_false_eq_eq_false_and_eq_false /-
@[simp]
theorem Bool.or_eq_false_eq_eq_false_and_eq_false (a b : Bool) : ((a || b) = ff) = (a = ff ∧ b = ff) := by
  cases a <;> cases b <;> simp
-/

#print Bool.not_eq_false_eq_eq_true /-
@[simp]
theorem Bool.not_eq_false_eq_eq_true (a : Bool) : (not a = ff) = (a = tt) := by cases a <;> simp
-/

#print Bool.coe_false /-
@[simp]
theorem Bool.coe_false : ↑ff = False :=
  show (ff = tt) = False by simp
-/

#print Bool.coe_true /-
@[simp]
theorem Bool.coe_true : ↑tt = True :=
  show (tt = tt) = True by simp
-/

#print Bool.coe_sort_false /-
@[simp]
theorem Bool.coe_sort_false : ↥ff = False :=
  show (ff = tt) = False by simp
-/

#print Bool.coe_sort_true /-
@[simp]
theorem Bool.coe_sort_true : ↥tt = True :=
  show (tt = tt) = True by simp
-/

#print Bool.decide_iff /-
@[simp]
theorem Bool.decide_iff (p : Prop) [d : Decidable p] : decide p = tt ↔ p :=
  match d with
  | is_true hp => ⟨fun h => hp, fun _ => rfl⟩
  | is_false hnp => ⟨fun h => Bool.noConfusion h, fun hp => absurd hp hnp⟩
-/

#print Bool.decide_true /-
theorem Bool.decide_true {p : Prop} [Decidable p] : p → decide p :=
  (Bool.decide_iff p).2
-/

/- warning: to_bool_tt clashes with to_bool_true -> Bool.decide_true
Case conversion may be inaccurate. Consider using '#align to_bool_tt Bool.decide_trueₓ'. -/
#print Bool.decide_true /-
theorem Bool.decide_true {p : Prop} [Decidable p] : p → decide p = tt :=
  Bool.decide_true
-/

#print Bool.of_decide_true /-
theorem Bool.of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (Bool.decide_iff p).1
-/

#print Bool.bool_iff_false /-
theorem Bool.bool_iff_false {b : Bool} : ¬b ↔ b = ff := by cases b <;> exact by decide
-/

#print Bool.bool_eq_false /-
theorem Bool.bool_eq_false {b : Bool} : ¬b → b = ff :=
  Bool.bool_iff_false.1
-/

#print Bool.decide_false_iff /-
@[simp]
theorem Bool.decide_false_iff (p : Prop) [Decidable p] : decide p = ff ↔ ¬p :=
  Bool.bool_iff_false.symm.trans (not_congr (Bool.decide_iff _))
-/

#print Bool.decide_false /-
theorem Bool.decide_false {p : Prop} [Decidable p] : ¬p → decide p = ff :=
  (Bool.decide_false_iff p).2
-/

#print Bool.of_decide_false /-
theorem Bool.of_decide_false {p : Prop} [Decidable p] : decide p = ff → ¬p :=
  (Bool.decide_false_iff p).1
-/

#print Bool.decide_congr /-
theorem Bool.decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q := by
  induction' h' : to_bool q with
  exact Bool.decide_false (mt h.1 <| Bool.of_decide_false h')
  exact Bool.decide_true (h.2 <| Bool.of_decide_true h')
-/

#print Bool.or_coe_iff /-
@[simp]
theorem Bool.or_coe_iff (a b : Bool) : a || b ↔ a ∨ b := by cases a <;> cases b <;> exact by decide
-/

#print Bool.and_coe_iff /-
@[simp]
theorem Bool.and_coe_iff (a b : Bool) : a && b ↔ a ∧ b := by cases a <;> cases b <;> exact by decide
-/

#print Bool.xor_coe_iff /-
@[simp]
theorem Bool.xor_coe_iff (a b : Bool) : xor a b ↔ Xor' a b := by cases a <;> cases b <;> exact by decide
-/

#print Bool.ite_eq_true_distrib /-
@[simp]
theorem Bool.ite_eq_true_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = tt) = if c then a = tt else b = tt := by by_cases c <;> simp [*]
-/

#print Bool.ite_eq_false_distrib /-
@[simp]
theorem Bool.ite_eq_false_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = ff) = if c then a = ff else b = ff := by by_cases c <;> simp [*]
-/

