/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Wf

universe u v

/- warning: ex_of_psig -> ex_of_psig is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop}, (PSigma.{succ u, 0} α (fun (x : α) => p x)) -> (Exists.{succ u} α (fun (x : α) => p x))
but is expected to have type
  forall {α : Sort.{u_1}} {p : α -> Prop}, (PSigma.{u_1, 0} α (fun (x : α) => p x)) -> (Exists.{u_1} α (fun (x : α) => p x))
Case conversion may be inaccurate. Consider using '#align ex_of_psig ex_of_psigₓ'. -/
theorem ex_of_psig {α : Type u} {p : α → Prop} : (Σ'x, p x) → ∃ x, p x
  | ⟨x, hx⟩ => ⟨x, hx⟩
#align ex_of_psig ex_of_psig

section

variable {α : Type u} {β : α → Type v}

#print Sigma.eq /-
protected theorem Sigma.eq :
    ∀ {p₁ p₂ : Σa : α, β a} (h₁ : p₁.1 = p₂.1), (Eq.recOn h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨a, b⟩, ⟨a, b⟩, rfl, rfl => rfl
#align sigma.eq Sigma.eq
-/

end

section

variable {α : Sort u} {β : α → Sort v}

#print PSigma.eq /-
protected theorem PSigma.eq :
    ∀ {p₁ p₂ : PSigma β} (h₁ : p₁.1 = p₂.1), (Eq.recOn h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨a, b⟩, ⟨a, b⟩, rfl, rfl => rfl
#align psigma.eq PSigma.eq
-/

end

