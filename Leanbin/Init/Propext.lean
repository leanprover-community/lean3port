/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Logic

#align_import init.propext from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

#print propext /-
axiom propext {a b : Prop} : (a ↔ b) → a = b
#align propext propext
-/

/-! # Additional congruence lemmas. -/


universe u v

#print forall_congr /-
theorem forall_congr {a : Sort u} {p q : a → Prop} (h : ∀ x, p x = q x) : (∀ x, p x) = ∀ x, q x :=
  propext (forall_congr' fun a => (h a).to_iff)
#align forall_congr_eq forall_congr
-/

#print imp_congr_eq /-
theorem imp_congr_eq {a b c d : Prop} (h₁ : a = c) (h₂ : b = d) : (a → b) = (c → d) :=
  propext (imp_congr h₁.to_iff h₂.to_iff)
#align imp_congr_eq imp_congr_eq
-/

#print imp_congr_ctx_eq /-
theorem imp_congr_ctx_eq {a b c d : Prop} (h₁ : a = c) (h₂ : c → b = d) : (a → b) = (c → d) :=
  propext (imp_congr_ctx h₁.to_iff fun hc => (h₂ hc).to_iff)
#align imp_congr_ctx_eq imp_congr_ctx_eq
-/

#print eq_true /-
theorem eq_true {a : Prop} (h : a) : a = True :=
  propext (iff_true_intro h)
#align eq_true_intro eq_true
-/

#print eq_false /-
theorem eq_false {a : Prop} (h : ¬a) : a = False :=
  propext (iff_false_intro h)
#align eq_false_intro eq_false
-/

theorem Iff.to_eq {a b : Prop} (h : a ↔ b) : a = b :=
  propext h
#align iff.to_eq Iff.to_eq

#print iff_eq_eq /-
theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) :=
  propext (Iff.intro (fun h => Iff.to_eq h) fun h => h.to_iff)
#align iff_eq_eq iff_eq_eq
-/

