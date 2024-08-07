/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Bool.Basic
import Leanbin.Init.Meta.Default

#align_import init.data.bool.lemmas from "leanprover-community/lean"@"9af482290ef68e8aaa5ead01aa7b09b7be7019fd"

attribute [simp] cond or and not xor

@[simp]
theorem cond_a_a.{u} {α : Type u} (b : Bool) (a : α) : cond b a a = a := by cases b <;> simp
#align cond_a_a cond_a_a

#print and_self /-
@[simp]
theorem and_self (b : Bool) : (b && b) = b := by cases b <;> simp
#align band_self and_self
-/

#print and_true /-
@[simp]
theorem and_true (b : Bool) : (b && true) = b := by cases b <;> simp
#align band_tt and_true
-/

#print and_false /-
@[simp]
theorem and_false (b : Bool) : (b && false) = false := by cases b <;> simp
#align band_ff and_false
-/

#print true_and /-
@[simp]
theorem true_and (b : Bool) : (true && b) = b := by cases b <;> simp
#align tt_band true_and
-/

#print false_and /-
@[simp]
theorem false_and (b : Bool) : (false && b) = false := by cases b <;> simp
#align ff_band false_and
-/

#print or_self /-
@[simp]
theorem or_self (b : Bool) : (b || b) = b := by cases b <;> simp
#align bor_self or_self
-/

#print or_true /-
@[simp]
theorem or_true (b : Bool) : (b || true) = true := by cases b <;> simp
#align bor_tt or_true
-/

#print or_false /-
@[simp]
theorem or_false (b : Bool) : (b || false) = b := by cases b <;> simp
#align bor_ff or_false
-/

#print true_or /-
@[simp]
theorem true_or (b : Bool) : (true || b) = true := by cases b <;> simp
#align tt_bor true_or
-/

#print false_or /-
@[simp]
theorem false_or (b : Bool) : (false || b) = b := by cases b <;> simp
#align ff_bor false_or
-/

/- warning: bxor_self clashes with xor_self -> xor_self
Case conversion may be inaccurate. Consider using '#align bxor_self xor_selfₓ'. -/
#print xor_self /-
@[simp]
theorem xor_self (b : Bool) : xor b b = false := by cases b <;> simp
#align bxor_self xor_self
-/

/- warning: bxor_tt clashes with xor_true -> xor_true
Case conversion may be inaccurate. Consider using '#align bxor_tt xor_trueₓ'. -/
#print xor_true /-
@[simp]
theorem xor_true (b : Bool) : xor b true = not b := by cases b <;> simp
#align bxor_tt xor_true
-/

/- warning: bxor_ff clashes with xor_false -> xor_false
Case conversion may be inaccurate. Consider using '#align bxor_ff xor_falseₓ'. -/
#print xor_false /-
theorem xor_false (b : Bool) : xor b false = b := by cases b <;> simp
#align bxor_ff xor_false
-/

@[simp]
theorem true_xor (b : Bool) : xor true b = not b := by cases b <;> simp
#align tt_bxor true_xor

theorem false_xor (b : Bool) : xor false b = b := by cases b <;> simp
#align ff_bxor false_xor

@[simp]
theorem not_not (b : Bool) : not (not b) = b := by cases b <;> simp
#align bnot_bnot not_not

#print Bool.true_eq_false_eq_False /-
theorem Bool.true_eq_false_eq_False : ¬true = false := by contradiction
#align tt_eq_ff_eq_false Bool.true_eq_false_eq_False
-/

#print Bool.false_eq_true_eq_False /-
theorem Bool.false_eq_true_eq_False : ¬false = true := by contradiction
#align ff_eq_tt_eq_false Bool.false_eq_true_eq_False
-/

#print Bool.eq_false_eq_not_eq_true /-
@[simp]
theorem Bool.eq_false_eq_not_eq_true (b : Bool) : (¬b = true) = (b = false) := by cases b <;> simp
#align eq_ff_eq_not_eq_tt Bool.eq_false_eq_not_eq_true
-/

@[simp]
theorem eq_true_eq_not_eq_false (b : Bool) : (¬b = false) = (b = true) := by cases b <;> simp
#align eq_tt_eq_not_eq_ff eq_true_eq_not_eq_false

#print Bool.eq_false_of_not_eq_true /-
theorem Bool.eq_false_of_not_eq_true {b : Bool} : ¬b = true → b = false :=
  Eq.mp (Bool.eq_false_eq_not_eq_true b)
#align eq_ff_of_not_eq_tt Bool.eq_false_of_not_eq_true
-/

#print Bool.eq_true_of_not_eq_false /-
theorem Bool.eq_true_of_not_eq_false {b : Bool} : ¬b = false → b = true :=
  Eq.mp (eq_true_eq_not_eq_false b)
#align eq_tt_of_not_eq_ff Bool.eq_true_of_not_eq_false
-/

#print Bool.and_eq_true_eq_eq_true_and_eq_true /-
@[simp]
theorem Bool.and_eq_true_eq_eq_true_and_eq_true (a b : Bool) :
    ((a && b) = true) = (a = true ∧ b = true) := by cases a <;> cases b <;> simp
#align band_eq_true_eq_eq_tt_and_eq_tt Bool.and_eq_true_eq_eq_true_and_eq_true
-/

#print Bool.or_eq_true_eq_eq_true_or_eq_true /-
@[simp]
theorem Bool.or_eq_true_eq_eq_true_or_eq_true (a b : Bool) :
    ((a || b) = true) = (a = true ∨ b = true) := by cases a <;> cases b <;> simp
#align bor_eq_true_eq_eq_tt_or_eq_tt Bool.or_eq_true_eq_eq_true_or_eq_true
-/

#print Bool.not_eq_true_eq_eq_false /-
@[simp]
theorem Bool.not_eq_true_eq_eq_false (a : Bool) : (not a = true) = (a = false) := by
  cases a <;> simp
#align bnot_eq_true_eq_eq_ff Bool.not_eq_true_eq_eq_false
-/

#print Bool.and_eq_false_eq_eq_false_or_eq_false /-
@[simp]
theorem Bool.and_eq_false_eq_eq_false_or_eq_false (a b : Bool) :
    ((a && b) = false) = (a = false ∨ b = false) := by cases a <;> cases b <;> simp
#align band_eq_false_eq_eq_ff_or_eq_ff Bool.and_eq_false_eq_eq_false_or_eq_false
-/

#print Bool.or_eq_false_eq_eq_false_and_eq_false /-
@[simp]
theorem Bool.or_eq_false_eq_eq_false_and_eq_false (a b : Bool) :
    ((a || b) = false) = (a = false ∧ b = false) := by cases a <;> cases b <;> simp
#align bor_eq_false_eq_eq_ff_and_eq_ff Bool.or_eq_false_eq_eq_false_and_eq_false
-/

#print Bool.not_eq_false_eq_eq_true /-
@[simp]
theorem Bool.not_eq_false_eq_eq_true (a : Bool) : (not a = false) = (a = true) := by
  cases a <;> simp
#align bnot_eq_ff_eq_eq_tt Bool.not_eq_false_eq_eq_true
-/

#print Bool.coe_false /-
@[simp]
theorem Bool.coe_false : ↑false = False :=
  show (false = true) = False by simp
#align coe_ff Bool.coe_false
-/

#print Bool.coe_true /-
@[simp]
theorem Bool.coe_true : ↑true = True :=
  show (true = true) = True by simp
#align coe_tt Bool.coe_true
-/

#print Bool.coe_sort_false /-
@[simp]
theorem Bool.coe_sort_false : ↥false = False :=
  show (false = true) = False by simp
#align coe_sort_ff Bool.coe_sort_false
-/

#print Bool.coe_sort_true /-
@[simp]
theorem Bool.coe_sort_true : ↥true = True :=
  show (true = true) = True by simp
#align coe_sort_tt Bool.coe_sort_true
-/

#print Bool.decide_iff /-
@[simp]
theorem Bool.decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p :=
  match d with
  | is_true hp => ⟨fun h => hp, fun _ => rfl⟩
  | is_false hnp => ⟨fun h => Bool.noConfusion h, fun hp => absurd hp hnp⟩
#align to_bool_iff Bool.decide_iff
-/

#print Bool.decide_true /-
theorem Bool.decide_true {p : Prop} [Decidable p] : p → decide p :=
  (Bool.decide_iff p).2
#align to_bool_true Bool.decide_true
-/

/- warning: to_bool_tt clashes with to_bool_true -> Bool.decide_true
Case conversion may be inaccurate. Consider using '#align to_bool_tt Bool.decide_trueₓ'. -/
#print Bool.decide_true /-
theorem Bool.decide_true {p : Prop} [Decidable p] : p → decide p = true :=
  Bool.decide_true
#align to_bool_tt Bool.decide_true
-/

#print Bool.of_decide_true /-
theorem Bool.of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (Bool.decide_iff p).1
#align of_to_bool_true Bool.of_decide_true
-/

#print Bool.bool_iff_false /-
theorem Bool.bool_iff_false {b : Bool} : ¬b ↔ b = false := by cases b <;> exact by decide
#align bool_iff_false Bool.bool_iff_false
-/

#print Bool.bool_eq_false /-
theorem Bool.bool_eq_false {b : Bool} : ¬b → b = false :=
  Bool.bool_iff_false.1
#align bool_eq_false Bool.bool_eq_false
-/

#print Bool.decide_false_iff /-
@[simp]
theorem Bool.decide_false_iff (p : Prop) [Decidable p] : decide p = false ↔ ¬p :=
  Bool.bool_iff_false.symm.trans (not_congr (Bool.decide_iff _))
#align to_bool_ff_iff Bool.decide_false_iff
-/

#print Bool.decide_false /-
theorem Bool.decide_false {p : Prop} [Decidable p] : ¬p → decide p = false :=
  (Bool.decide_false_iff p).2
#align to_bool_ff Bool.decide_false
-/

#print Bool.of_decide_false /-
theorem Bool.of_decide_false {p : Prop} [Decidable p] : decide p = false → ¬p :=
  (Bool.decide_false_iff p).1
#align of_to_bool_ff Bool.of_decide_false
-/

#print Bool.decide_congr /-
theorem Bool.decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  induction' h' : to_bool q with
  exact Bool.decide_false (mt h.1 <| Bool.of_decide_false h')
  exact Bool.decide_true (h.2 <| Bool.of_decide_true h')
#align to_bool_congr Bool.decide_congr
-/

#print Bool.or_eq_true_iff /-
@[simp]
theorem Bool.or_eq_true_iff (a b : Bool) : a || b ↔ a ∨ b := by
  cases a <;> cases b <;> exact by decide
#align bor_coe_iff Bool.or_eq_true_iff
-/

#print Bool.and_eq_true_iff /-
@[simp]
theorem Bool.and_eq_true_iff (a b : Bool) : a && b ↔ a ∧ b := by
  cases a <;> cases b <;> exact by decide
#align band_coe_iff Bool.and_eq_true_iff
-/

#print Bool.coe_xor_iff /-
@[simp]
theorem Bool.coe_xor_iff (a b : Bool) : xor a b ↔ Xor' a b := by
  cases a <;> cases b <;> exact by decide
#align bxor_coe_iff Bool.coe_xor_iff
-/

@[simp]
theorem ite_eq_true_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = true) = if c then a = true else b = true := by by_cases c <;> simp [*]
#align ite_eq_tt_distrib ite_eq_true_distrib

@[simp]
theorem ite_eq_false_distrib (c : Prop) [Decidable c] (a b : Bool) :
    ((if c then a else b) = false) = if c then a = false else b = false := by
  by_cases c <;> simp [*]
#align ite_eq_ff_distrib ite_eq_false_distrib

