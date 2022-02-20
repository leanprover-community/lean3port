/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Propext
import Leanbin.Init.Classical

-- Lemmas use by the congruence closure module 
-- Lemmas use by the congruence closure module
theorem iff_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ↔ b) = b :=
  h.symm ▸ propext (true_iffₓ _)

theorem iff_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ↔ b) = a :=
  h.symm ▸ propext (iff_trueₓ _)

theorem iff_eq_true_of_eq {a b : Prop} (h : a = b) : (a ↔ b) = True :=
  h ▸ propext (iff_selfₓ _)

theorem and_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ∧ b) = b :=
  h.symm ▸ propext (true_andₓ _)

theorem and_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ∧ b) = a :=
  h.symm ▸ propext (and_trueₓ _)

theorem and_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a ∧ b) = False :=
  h.symm ▸ propext (false_andₓ _)

theorem and_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a ∧ b) = False :=
  h.symm ▸ propext (and_falseₓ _)

theorem and_eq_of_eq {a b : Prop} (h : a = b) : (a ∧ b) = a :=
  h ▸ propext (and_selfₓ _)

theorem or_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ∨ b) = True :=
  h.symm ▸ propext (true_orₓ _)

theorem or_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ∨ b) = True :=
  h.symm ▸ propext (or_trueₓ _)

theorem or_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a ∨ b) = b :=
  h.symm ▸ propext (false_orₓ _)

theorem or_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a ∨ b) = a :=
  h.symm ▸ propext (or_falseₓ _)

theorem or_eq_of_eq {a b : Prop} (h : a = b) : (a ∨ b) = a :=
  h ▸ propext (or_selfₓ _)

theorem imp_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a → b) = b :=
  h.symm ▸ propext (Iff.intro (fun h => h trivialₓ) fun h₁ h₂ => h₁)

theorem imp_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a → b) = True :=
  h.symm ▸ propext (Iff.intro (fun h => trivialₓ) fun h₁ h₂ => h₁)

theorem imp_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a → b) = True :=
  h.symm ▸ propext (Iff.intro (fun h => trivialₓ) fun h₁ h₂ => False.elim h₂)

theorem imp_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a → b) = Not a :=
  h.symm ▸ propext (Iff.intro (fun h => h) fun hna ha => hna ha)

/- Remark: the congruence closure module will only use the following lemma is
   cc_config.em is tt. -/
theorem not_imp_eq_of_eq_false_right {a b : Prop} (h : b = False) : (Not a → b) = a :=
  h.symm ▸ propext (Iff.intro (fun h' => Classical.by_contradiction fun hna => h' hna) fun ha hna => hna ha)

theorem imp_eq_true_of_eq {a b : Prop} (h : a = b) : (a → b) = True :=
  h ▸ propext (Iff.intro (fun h => trivialₓ) fun h ha => ha)

theorem not_eq_of_eq_true {a : Prop} (h : a = True) : Not a = False :=
  h.symm ▸ propext not_true

theorem not_eq_of_eq_false {a : Prop} (h : a = False) : Not a = True :=
  h.symm ▸ propext not_false_iff

theorem false_of_a_eq_not_a {a : Prop} (h : a = Not a) : False :=
  have : Not a := fun ha => absurd ha (Eq.mp h ha)
  absurd (Eq.mpr h this) this

universe u

theorem if_eq_of_eq_true {c : Prop} [d : Decidable c] {α : Sort u} (t e : α) (h : c = True) : @ite α c d t e = t :=
  if_pos (of_eq_true h)

theorem if_eq_of_eq_false {c : Prop} [d : Decidable c] {α : Sort u} (t e : α) (h : c = False) : @ite α c d t e = e :=
  if_neg (not_of_eq_false h)

theorem if_eq_of_eq (c : Prop) [d : Decidable c] {α : Sort u} {t e : α} (h : t = e) : @ite α c d t e = t :=
  match d with
  | is_true hc => rfl
  | is_false hnc => Eq.symm h

theorem eq_true_of_and_eq_true_left {a b : Prop} (h : (a ∧ b) = True) : a = True :=
  eq_true_intro (And.left (of_eq_true h))

theorem eq_true_of_and_eq_true_right {a b : Prop} (h : (a ∧ b) = True) : b = True :=
  eq_true_intro (And.right (of_eq_true h))

theorem eq_false_of_or_eq_false_left {a b : Prop} (h : (a ∨ b) = False) : a = False :=
  eq_false_intro fun ha => False.elim (Eq.mp h (Or.inl ha))

theorem eq_false_of_or_eq_false_right {a b : Prop} (h : (a ∨ b) = False) : b = False :=
  eq_false_intro fun hb => False.elim (Eq.mp h (Or.inr hb))

theorem eq_false_of_not_eq_true {a : Prop} (h : Not a = True) : a = False :=
  eq_false_intro fun ha => absurd ha (Eq.mpr h trivialₓ)

/- Remark: the congruence closure module will only use the following lemma is
   cc_config.em is tt. -/
theorem eq_true_of_not_eq_false {a : Prop} (h : Not a = False) : a = True :=
  eq_true_intro (Classical.by_contradiction fun hna => Eq.mp h hna)

theorem ne_of_eq_of_ne {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b ≠ c) : a ≠ c :=
  h₁.symm ▸ h₂

theorem ne_of_ne_of_eq {α : Sort u} {a b c : α} (h₁ : a ≠ b) (h₂ : b = c) : a ≠ c :=
  h₂ ▸ h₁

