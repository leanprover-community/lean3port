/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Quotient types.
-/
prelude
import Leanbin.Init.Data.Sigma.Basic
import Leanbin.Init.Logic
import Leanbin.Init.Propext
import Leanbin.Init.Data.Setoid

-- We import propext here, otherwise we would need a quot.lift for propositions.
universe u v

-- iff can now be used to do substitutions in a calculation
@[subst]
theorem iff_subst {a b : Prop} {p : Prop → Prop} (h₁ : a ↔ b) (h₂ : p a) : p b :=
  Eq.subst (propext h₁) h₂

namespace Quot

protected theorem lift_beta {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) (c : ∀ a b, r a b → f a = f b)
    (a : α) : lift f c (Quot.mk r a) = f a :=
  rfl

protected theorem ind_beta {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (p : ∀ a, β (Quot.mk r a)) (a : α) :
    (ind p (Quot.mk r a) : β (Quot.mk r a)) = p a :=
  rfl

@[elabAsElim]
protected theorem induction_on {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r)
    (h : ∀ a, β (Quot.mk r a)) : β q :=
  ind h q

section

variable {α : Sort u}

variable {r : α → α → Prop}

variable {β : Quot r → Sort v}

-- mathport name: «expr⟦ ⟧»
local notation:arg "⟦" a "⟧" => Quot.mk r a

protected theorem indep_coherent (f : ∀ a, β ⟦a⟧)
    (h : ∀ (a b : α) (p : r a b), (Eq.ndrec (f a) (sound p) : β ⟦b⟧) = f b) :
    ∀ a b, r a b → Quot.indep f a = Quot.indep f b := fun a b e => PSigma.eq (sound e) (h a b e)

protected theorem lift_indep_pr1 (f : ∀ a, β ⟦a⟧)
    (h : ∀ (a b : α) (p : r a b), (Eq.ndrec (f a) (sound p) : β ⟦b⟧) = f b) (q : Quot r) :
    (lift (Quot.indep f) (Quot.indep_coherent f h) q).1 = q :=
  Quot.liftIndepPr1 f h q

end

end Quot

namespace Quotient

-- mathport name: «expr⟦ ⟧»
local notation:arg "⟦" a "⟧" => Quotient.mk _ a

@[elabAsElim]
protected theorem induction_on {α : Sort u} [s : Setoid α] {β : Quotient s → Prop} (q : Quotient s)
    (h : ∀ a, β ⟦a⟧) : β q :=
  Quot.induction_on q h


section

universe u_a u_b u_c

variable {α : Sort u_a} {β : Sort u_b} {φ : Sort u_c}

variable [s₁ : Setoid α] [s₂ : Setoid β]

include s₁ s₂

@[elabAsElim] private def ind' := @Quotient.ind

@[elabAsElim]
protected theorem induction_on₂ {φ : Quotient s₁ → Quotient s₂ → Prop} (q₁ : Quotient s₁) (q₂ : Quotient s₂)
    (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  ind' (fun a₁ => Quotient.ind (fun a₂ => h a₁ a₂) q₂) q₁

@[elabAsElim]
protected theorem induction_on₃ [s₃ : Setoid φ] {δ : Quotient s₁ → Quotient s₂ → Quotient s₃ → Prop}
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) (q₃ : Quotient s₃) (h : ∀ a b c, δ ⟦a⟧ ⟦b⟧ ⟦c⟧) : δ q₁ q₂ q₃ :=
  ind' (fun a₁ => ind' (fun a₂ => Quotient.ind (fun a₃ => h a₁ a₂ a₃) q₃) q₂) q₁

end

end Quotient

section

variable {α : Type u}

variable (r : α → α → Prop)

inductive EqvGen : α → α → Prop
  | rel : ∀ x y, r x y → EqvGen x y
  | refl : ∀ x, EqvGen x x
  | symm : ∀ x y, EqvGen x y → EqvGen y x
  | trans : ∀ x y z, EqvGen x y → EqvGen y z → EqvGen x z

theorem EqvGen.is_equivalence : Equivalence (@EqvGen α r) :=
  mk_equivalence _ EqvGen.refl EqvGen.symm EqvGen.trans

theorem EqvGen.isEquivalence : Equivalence (@EqvGen α r) :=
  ⟨EqvGen.refl, EqvGen.symm _ _, EqvGen.trans _ _ _⟩

def EqvGen.setoid : Setoid α :=
  Setoid.mk _ (EqvGen.isEquivalence r)

theorem Quot.exact {a b : α} (H : Quot.mk r a = Quot.mk r b) : EqvGen r a b :=
  @Quotient.exact _ (EqvGen.setoid r) a b
    (@congr_arg _ _ _ _ (Quot.lift (@Quotient.mk _ (EqvGen.setoid r)) fun x y h => Quot.sound (EqvGen.rel x y h)) H)

theorem Quot.eqv_gen_sound {r : α → α → Prop} {a b : α} (H : EqvGen r a b) : Quot.mk r a = Quot.mk r b :=
  EqvGen.recOn H (fun x y h => Quot.sound h) (fun x => rfl) (fun x y _ IH => Eq.symm IH) fun x y z _ _ IH₁ IH₂ =>
    Eq.trans IH₁ IH₂

end

