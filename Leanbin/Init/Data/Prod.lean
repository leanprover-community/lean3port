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

/- warning: prod.mk.eta -> Prod.mk.eta is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} {p : Prod.{u v} α β}, Eq.{(max (succ u) (succ v))} (Prod.{u v} α β) (Prod.mk.{u v} α β (Prod.fst.{u v} α β p) (Prod.snd.{u v} α β p)) p
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β}, Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.mk.{u_1 u_2} α β (Prod.fst.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β p)) p
Case conversion may be inaccurate. Consider using '#align prod.mk.eta Prod.mk.etaₓ'. -/
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
      | is_true e₂ => isTrue (Eq.recOn e₁ (Eq.recOn e₂ rfl))
      | is_false n₂ => isFalse fun h => Prod.noConfusion h fun e₁' e₂' => absurd e₂' n₂
    | is_false n₁ => isFalse fun h => Prod.noConfusion h fun e₁' e₂' => absurd e₁' n₁

end

def Prod.map.{u₁, u₂, v₁, v₂} {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂} (f : α₁ → α₂) (g : β₁ → β₂)
    (x : α₁ × β₁) : α₂ × β₂ :=
  (f x.1, g x.2)

