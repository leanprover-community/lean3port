/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.cc_lemmas
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Propext
import Leanbin.Init.Classical

/-! Lemmas use by the congruence closure module -/


#print iff_eq_of_eq_true_left /-
theorem iff_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ↔ b) = b :=
  h.symm ▸ propext (true_iff_iff _)
#align iff_eq_of_eq_true_left iff_eq_of_eq_true_left
-/

#print iff_eq_of_eq_true_right /-
theorem iff_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ↔ b) = a :=
  h.symm ▸ propext (iff_true_iff _)
#align iff_eq_of_eq_true_right iff_eq_of_eq_true_right
-/

#print iff_eq_true_of_eq /-
theorem iff_eq_true_of_eq {a b : Prop} (h : a = b) : (a ↔ b) = True :=
  h ▸ propext (iff_self_iff _)
#align iff_eq_true_of_eq iff_eq_true_of_eq
-/

#print and_eq_of_eq_true_left /-
theorem and_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ∧ b) = b :=
  h.symm ▸ propext (true_and_iff _)
#align and_eq_of_eq_true_left and_eq_of_eq_true_left
-/

#print and_eq_of_eq_true_right /-
theorem and_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ∧ b) = a :=
  h.symm ▸ propext (and_true_iff _)
#align and_eq_of_eq_true_right and_eq_of_eq_true_right
-/

#print and_eq_of_eq_false_left /-
theorem and_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a ∧ b) = False :=
  h.symm ▸ propext (false_and_iff _)
#align and_eq_of_eq_false_left and_eq_of_eq_false_left
-/

#print and_eq_of_eq_false_right /-
theorem and_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a ∧ b) = False :=
  h.symm ▸ propext (and_false_iff _)
#align and_eq_of_eq_false_right and_eq_of_eq_false_right
-/

#print and_eq_of_eq /-
theorem and_eq_of_eq {a b : Prop} (h : a = b) : (a ∧ b) = a :=
  h ▸ propext (and_self_iff _)
#align and_eq_of_eq and_eq_of_eq
-/

#print or_eq_of_eq_true_left /-
theorem or_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ∨ b) = True :=
  h.symm ▸ propext (true_or_iff _)
#align or_eq_of_eq_true_left or_eq_of_eq_true_left
-/

#print or_eq_of_eq_true_right /-
theorem or_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ∨ b) = True :=
  h.symm ▸ propext (or_true_iff _)
#align or_eq_of_eq_true_right or_eq_of_eq_true_right
-/

#print or_eq_of_eq_false_left /-
theorem or_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a ∨ b) = b :=
  h.symm ▸ propext (false_or_iff _)
#align or_eq_of_eq_false_left or_eq_of_eq_false_left
-/

#print or_eq_of_eq_false_right /-
theorem or_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a ∨ b) = a :=
  h.symm ▸ propext (or_false_iff _)
#align or_eq_of_eq_false_right or_eq_of_eq_false_right
-/

#print or_eq_of_eq /-
theorem or_eq_of_eq {a b : Prop} (h : a = b) : (a ∨ b) = a :=
  h ▸ propext (or_self_iff _)
#align or_eq_of_eq or_eq_of_eq
-/

#print imp_eq_of_eq_true_left /-
theorem imp_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a → b) = b :=
  h.symm ▸ propext (Iff.intro (fun h => h trivial) fun h₁ h₂ => h₁)
#align imp_eq_of_eq_true_left imp_eq_of_eq_true_left
-/

#print imp_eq_of_eq_true_right /-
theorem imp_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a → b) = True :=
  h.symm ▸ propext (Iff.intro (fun h => trivial) fun h₁ h₂ => h₁)
#align imp_eq_of_eq_true_right imp_eq_of_eq_true_right
-/

#print imp_eq_of_eq_false_left /-
theorem imp_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a → b) = True :=
  h.symm ▸ propext (Iff.intro (fun h => trivial) fun h₁ h₂ => False.elim h₂)
#align imp_eq_of_eq_false_left imp_eq_of_eq_false_left
-/

#print imp_eq_of_eq_false_right /-
theorem imp_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a → b) = Not a :=
  h.symm ▸ propext (Iff.intro (fun h => h) fun hna ha => hna ha)
#align imp_eq_of_eq_false_right imp_eq_of_eq_false_right
-/

#print not_imp_eq_of_eq_false_right /-
/-- Remark: the congruence closure module will only use this lemma if
   cc_config.em is tt. -/
theorem not_imp_eq_of_eq_false_right {a b : Prop} (h : b = False) : (Not a → b) = a :=
  h.symm ▸
    propext
      (Iff.intro (fun h' => Classical.by_contradiction fun hna => h' hna) fun ha hna => hna ha)
#align not_imp_eq_of_eq_false_right not_imp_eq_of_eq_false_right
-/

#print imp_eq_true_of_eq /-
theorem imp_eq_true_of_eq {a b : Prop} (h : a = b) : (a → b) = True :=
  h ▸ propext (Iff.intro (fun h => trivial) fun h ha => ha)
#align imp_eq_true_of_eq imp_eq_true_of_eq
-/

#print not_eq_of_eq_true /-
theorem not_eq_of_eq_true {a : Prop} (h : a = True) : Not a = False :=
  h.symm ▸ propext not_true
#align not_eq_of_eq_true not_eq_of_eq_true
-/

#print not_eq_of_eq_false /-
theorem not_eq_of_eq_false {a : Prop} (h : a = False) : Not a = True :=
  h.symm ▸ propext not_false_iff
#align not_eq_of_eq_false not_eq_of_eq_false
-/

#print false_of_a_eq_not_a /-
theorem false_of_a_eq_not_a {a : Prop} (h : a = Not a) : False :=
  have : Not a := fun ha => absurd ha (Eq.mp h ha)
  absurd (Eq.mpr h this) this
#align false_of_a_eq_not_a false_of_a_eq_not_a
-/

universe u

#print if_eq_of_eq_true /-
theorem if_eq_of_eq_true {c : Prop} [d : Decidable c] {α : Sort u} (t e : α) (h : c = True) :
    @ite α c d t e = t :=
  if_pos (of_eq_true h)
#align if_eq_of_eq_true if_eq_of_eq_true
-/

#print if_eq_of_eq_false /-
theorem if_eq_of_eq_false {c : Prop} [d : Decidable c] {α : Sort u} (t e : α) (h : c = False) :
    @ite α c d t e = e :=
  if_neg (not_of_eq_false h)
#align if_eq_of_eq_false if_eq_of_eq_false
-/

#print if_eq_of_eq /-
theorem if_eq_of_eq (c : Prop) [d : Decidable c] {α : Sort u} {t e : α} (h : t = e) :
    @ite α c d t e = t :=
  match d with
  | is_true hc => rfl
  | is_false hnc => Eq.symm h
#align if_eq_of_eq if_eq_of_eq
-/

#print eq_true_of_and_eq_true_left /-
theorem eq_true_of_and_eq_true_left {a b : Prop} (h : (a ∧ b) = True) : a = True :=
  eq_true (And.left (of_eq_true h))
#align eq_true_of_and_eq_true_left eq_true_of_and_eq_true_left
-/

#print eq_true_of_and_eq_true_right /-
theorem eq_true_of_and_eq_true_right {a b : Prop} (h : (a ∧ b) = True) : b = True :=
  eq_true (And.right (of_eq_true h))
#align eq_true_of_and_eq_true_right eq_true_of_and_eq_true_right
-/

#print eq_false_of_or_eq_false_left /-
theorem eq_false_of_or_eq_false_left {a b : Prop} (h : (a ∨ b) = False) : a = False :=
  eq_false fun ha => False.elim (Eq.mp h (Or.inl ha))
#align eq_false_of_or_eq_false_left eq_false_of_or_eq_false_left
-/

#print eq_false_of_or_eq_false_right /-
theorem eq_false_of_or_eq_false_right {a b : Prop} (h : (a ∨ b) = False) : b = False :=
  eq_false fun hb => False.elim (Eq.mp h (Or.inr hb))
#align eq_false_of_or_eq_false_right eq_false_of_or_eq_false_right
-/

#print eq_false_of_not_eq_true /-
theorem eq_false_of_not_eq_true {a : Prop} (h : Not a = True) : a = False :=
  eq_false fun ha => absurd ha (Eq.mpr h trivial)
#align eq_false_of_not_eq_true eq_false_of_not_eq_true
-/

#print eq_true_of_not_eq_false /-
/-- Remark: the congruence closure module will only use this lemma if
   cc_config.em is tt. -/
theorem eq_true_of_not_eq_false {a : Prop} (h : Not a = False) : a = True :=
  eq_true (Classical.by_contradiction fun hna => Eq.mp h hna)
#align eq_true_of_not_eq_false eq_true_of_not_eq_false
-/

#print ne_of_eq_of_ne /-
theorem ne_of_eq_of_ne {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b ≠ c) : a ≠ c :=
  h₁.symm ▸ h₂
#align ne_of_eq_of_ne ne_of_eq_of_ne
-/

#print ne_of_ne_of_eq /-
theorem ne_of_ne_of_eq {α : Sort u} {a b c : α} (h₁ : a ≠ b) (h₂ : b = c) : a ≠ c :=
  h₂ ▸ h₁
#align ne_of_ne_of_eq ne_of_ne_of_eq
-/

