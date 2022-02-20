/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic

axiom propext {a b : Prop} : (a ↔ b) → a = b

-- Additional congruence lemmas.
universe u v

theorem forall_congr_eq {a : Sort u} {p q : a → Prop} (h : ∀ x, p x = q x) : (∀ x, p x) = ∀ x, q x :=
  propext (forall_congrₓ fun a => (h a).to_iff)

theorem imp_congr_eq {a b c d : Prop} (h₁ : a = c) (h₂ : b = d) : (a → b) = (c → d) :=
  propext (imp_congr h₁.to_iff h₂.to_iff)

theorem imp_congr_ctx_eq {a b c d : Prop} (h₁ : a = c) (h₂ : c → b = d) : (a → b) = (c → d) :=
  propext (imp_congr_ctx h₁.to_iff fun hc => (h₂ hc).to_iff)

theorem eq_true_intro {a : Prop} (h : a) : a = True :=
  propext (iff_true_intro h)

theorem eq_false_intro {a : Prop} (h : ¬a) : a = False :=
  propext (iff_false_intro h)

theorem Iff.to_eq {a b : Prop} (h : a ↔ b) : a = b :=
  propext h

theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) :=
  propext (Iff.intro (fun h => Iff.to_eq h) fun h => h.to_iff)

theorem eq_falseₓ {a : Prop} : (a = False) = ¬a :=
  have : (a ↔ False) = ¬a := propext (iff_falseₓ a)
  Eq.subst (@iff_eq_eq a False) this

theorem eq_trueₓ {a : Prop} : (a = True) = a :=
  have : (a ↔ True) = a := propext (iff_trueₓ a)
  Eq.subst (@iff_eq_eq a True) this

