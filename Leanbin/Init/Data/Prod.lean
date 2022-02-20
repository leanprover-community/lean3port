/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import Leanbin.Init.Logic

universe u v

section

variable {α : Type u} {β : Type v}

@[simp]
theorem Prod.mk.eta : ∀ {p : α × β}, (p.1, p.2) = p
  | (a, b) => rfl

instance [Inhabited α] [Inhabited β] : Inhabited (Prod α β) :=
  ⟨(default, default)⟩

instance [h₁ : DecidableEq α] [h₂ : DecidableEq β] : DecidableEq (α × β)
  | (a, b), (a', b') =>
    match h₁ a a' with
    | is_true e₁ =>
      match h₂ b b' with
      | is_true e₂ => isTrue (Eq.recOnₓ e₁ (Eq.recOnₓ e₂ rfl))
      | is_false n₂ => isFalse fun h => Prod.noConfusion h fun e₁' e₂' => absurd e₂' n₂
    | is_false n₁ => isFalse fun h => Prod.noConfusion h fun e₁' e₂' => absurd e₁' n₁

end

def Prod.map.{u₁, u₂, v₁, v₂} {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂} (f : α₁ → α₂) (g : β₁ → β₂)
    (x : α₁ × β₁) : α₂ × β₂ :=
  (f x.1, g x.2)

