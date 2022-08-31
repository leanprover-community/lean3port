/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import Leanbin.Init.Data.Subtype.Basic
import Leanbin.Init.Propext

namespace Classical

universe u v

noncomputable def inhabitedOfNonempty {α : Sort u} (h : Nonempty α) : Inhabited α :=
  ⟨choice h⟩

noncomputable def inhabitedOfExists {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : Inhabited α :=
  inhabitedOfNonempty (Exists.elim h fun w hw => ⟨w⟩)

-- the axiom of choice
theorem axiom_of_choice {α : Sort u} {β : α → Sort v} {r : ∀ x, β x → Prop} (h : ∀ x, ∃ y, r x y) :
    ∃ f : ∀ x, β x, ∀ x, r x (f x) :=
  ⟨_, fun x => choose_spec (h x)⟩

theorem prop_complete (a : Prop) : a = True ∨ a = False :=
  Or.elim (em a) (fun t => Or.inl (eq_true_intro t)) fun f => Or.inr (eq_false_intro f)

section Aux

@[elabAsElim]
theorem cases_true_false {p : Prop → Prop} (h1 : p True) (h2 : p False) (a : Prop) : p a :=
  Or.elim (prop_complete a) (fun ht : a = True => ht.symm ▸ h1) fun hf : a = False => hf.symm ▸ h2

theorem cases_on (a : Prop) {p : Prop → Prop} (h1 : p True) (h2 : p False) : p a :=
  cases_true_false h1 h2 a

-- this supercedes by_cases in decidable
theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  Decidable.byCases hpq hnpq

-- this supercedes by_contradiction in decidable
theorem by_contradiction {p : Prop} (h : ¬p → False) : p :=
  Decidable.by_contradiction h

theorem eq_false_or_eq_true (a : Prop) : a = False ∨ a = True :=
  (prop_complete a).symm

end Aux

end Classical

