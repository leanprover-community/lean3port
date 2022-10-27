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

axiom sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b

attribute [elab_as_elim] lift ind

protected theorem lift_beta {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) (c : ∀ a b, r a b → f a = f b)
    (a : α) : lift f c (Quot.mk r a) = f a :=
  rfl

protected theorem ind_beta {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (p : ∀ a, β (Quot.mk r a)) (a : α) :
    (ind p (Quot.mk r a) : β (Quot.mk r a)) = p a :=
  rfl

@[reducible, elab_as_elim]
protected def liftOn {α : Sort u} {β : Sort v} {r : α → α → Prop} (q : Quot r) (f : α → β)
    (c : ∀ a b, r a b → f a = f b) : β :=
  lift f c q

@[elab_as_elim]
protected theorem induction_on {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r)
    (h : ∀ a, β (Quot.mk r a)) : β q :=
  ind h q

theorem exists_rep {α : Sort u} {r : α → α → Prop} (q : Quot r) : ∃ a : α, Quot.mk r a = q :=
  Quot.induction_on q fun a => ⟨a, rfl⟩

section

variable {α : Sort u}

variable {r : α → α → Prop}

variable {β : Quot r → Sort v}

-- mathport name: «expr⟦ ⟧»
local notation:arg "⟦" a "⟧" => Quot.mk r a

@[reducible]
protected def indep (f : ∀ a, β ⟦a⟧) (a : α) : PSigma β :=
  ⟨⟦a⟧, f a⟩

protected theorem indep_coherent (f : ∀ a, β ⟦a⟧)
    (h : ∀ (a b : α) (p : r a b), (Eq.ndrec (f a) (sound p) : β ⟦b⟧) = f b) :
    ∀ a b, r a b → Quot.indep f a = Quot.indep f b := fun a b e => PSigma.eq (sound e) (h a b e)

protected theorem lift_indep_pr1 (f : ∀ a, β ⟦a⟧)
    (h : ∀ (a b : α) (p : r a b), (Eq.ndrec (f a) (sound p) : β ⟦b⟧) = f b) (q : Quot r) :
    (lift (Quot.indep f) (Quot.indep_coherent f h) q).1 = q :=
  Quot.ind (fun a : α => Eq.refl (Quot.indep f a).1) q

@[reducible, elab_as_elim]
protected def rec (f : ∀ a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b), (Eq.ndrec (f a) (sound p) : β ⟦b⟧) = f b)
    (q : Quot r) : β q :=
  Eq.recOn (Quot.lift_indep_pr1 f h q) (lift (Quot.indep f) (Quot.indep_coherent f h) q).2

@[reducible, elab_as_elim]
protected def recOn (q : Quot r) (f : ∀ a, β ⟦a⟧)
    (h : ∀ (a b : α) (p : r a b), (Eq.ndrec (f a) (sound p) : β ⟦b⟧) = f b) : β q :=
  Quot.rec f h q

@[reducible, elab_as_elim]
protected def recOnSubsingleton [h : ∀ a, Subsingleton (β ⟦a⟧)] (q : Quot r) (f : ∀ a, β ⟦a⟧) : β q :=
  Quot.rec f (fun a b h => Subsingleton.elim _ (f b)) q

@[reducible, elab_as_elim]
protected def hrecOn (q : Quot r) (f : ∀ a, β ⟦a⟧) (c : ∀ (a b : α) (p : r a b), HEq (f a) (f b)) : β q :=
  Quot.recOn q f fun a b p =>
    eq_of_heq
      (calc
        HEq (Eq.ndrec (f a) (sound p) : β ⟦b⟧) (f a) := eq_rec_heq (sound p) (f a)
        HEq _ (f b) := c a b p
        )

end

end Quot

def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.R

namespace Quotient

protected def mk {α : Sort u} [s : Setoid α] (a : α) : Quotient s :=
  Quot.mk Setoid.R a

-- mathport name: «expr⟦ ⟧»
notation:arg "⟦" a "⟧" => Quotient.mk a

theorem sound {α : Sort u} [s : Setoid α] {a b : α} : a ≈ b → ⟦a⟧ = ⟦b⟧ :=
  Quot.sound

@[reducible, elab_as_elim]
protected def lift {α : Sort u} {β : Sort v} [s : Setoid α] (f : α → β) : (∀ a b, a ≈ b → f a = f b) → Quotient s → β :=
  Quot.lift f

@[elab_as_elim]
protected theorem ind {α : Sort u} [s : Setoid α] {β : Quotient s → Prop} : (∀ a, β ⟦a⟧) → ∀ q, β q :=
  Quot.ind

@[reducible, elab_as_elim]
protected def liftOn {α : Sort u} {β : Sort v} [s : Setoid α] (q : Quotient s) (f : α → β)
    (c : ∀ a b, a ≈ b → f a = f b) : β :=
  Quot.liftOn q f c

@[elab_as_elim]
protected theorem induction_on {α : Sort u} [s : Setoid α] {β : Quotient s → Prop} (q : Quotient s) (h : ∀ a, β ⟦a⟧) :
    β q :=
  Quot.induction_on q h

theorem exists_rep {α : Sort u} [s : Setoid α] (q : Quotient s) : ∃ a : α, ⟦a⟧ = q :=
  Quot.exists_rep q

section

variable {α : Sort u}

variable [s : Setoid α]

variable {β : Quotient s → Sort v}

protected def rec (f : ∀ a, β ⟦a⟧) (h : ∀ (a b : α) (p : a ≈ b), (Eq.ndrec (f a) (Quotient.sound p) : β ⟦b⟧) = f b)
    (q : Quotient s) : β q :=
  Quot.rec f h q

@[reducible, elab_as_elim]
protected def recOn (q : Quotient s) (f : ∀ a, β ⟦a⟧)
    (h : ∀ (a b : α) (p : a ≈ b), (Eq.ndrec (f a) (Quotient.sound p) : β ⟦b⟧) = f b) : β q :=
  Quot.recOn q f h

@[reducible, elab_as_elim]
protected def recOnSubsingleton [h : ∀ a, Subsingleton (β ⟦a⟧)] (q : Quotient s) (f : ∀ a, β ⟦a⟧) : β q :=
  @Quot.recOnSubsingleton _ _ _ h q f

@[reducible, elab_as_elim]
protected def hrecOn (q : Quotient s) (f : ∀ a, β ⟦a⟧) (c : ∀ (a b : α) (p : a ≈ b), HEq (f a) (f b)) : β q :=
  Quot.hrecOn q f c

end

section

universe u_a u_b u_c

variable {α : Sort u_a} {β : Sort u_b} {φ : Sort u_c}

variable [s₁ : Setoid α] [s₂ : Setoid β]

include s₁ s₂

@[reducible, elab_as_elim]
protected def lift₂ (f : α → β → φ) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (q₁ : Quotient s₁)
    (q₂ : Quotient s₂) : φ :=
  Quotient.lift (fun a₁ : α => Quotient.lift (f a₁) (fun a b : β => c a₁ a a₁ b (Setoid.refl a₁)) q₂)
    (fun (a b : α) (h : a ≈ b) =>
      @Quotient.ind β s₂
        (fun a_1 : Quotient s₂ =>
          Quotient.lift (f a) (fun a_1 b : β => c a a_1 a b (Setoid.refl a)) a_1 =
            Quotient.lift (f b) (fun a b_1 : β => c b a b b_1 (Setoid.refl b)) a_1)
        (fun a' : β => c a a' b a' h (Setoid.refl a')) q₂)
    q₁

@[reducible, elab_as_elim]
protected def liftOn₂ (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α → β → φ)
    (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : φ :=
  Quotient.lift₂ f c q₁ q₂

@[elab_as_elim]
protected theorem ind₂ {φ : Quotient s₁ → Quotient s₂ → Prop} (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) (q₁ : Quotient s₁)
    (q₂ : Quotient s₂) : φ q₁ q₂ :=
  Quotient.ind (fun a₁ => Quotient.ind (fun a₂ => h a₁ a₂) q₂) q₁

@[elab_as_elim]
protected theorem induction_on₂ {φ : Quotient s₁ → Quotient s₂ → Prop} (q₁ : Quotient s₁) (q₂ : Quotient s₂)
    (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  Quotient.ind (fun a₁ => Quotient.ind (fun a₂ => h a₁ a₂) q₂) q₁

@[elab_as_elim]
protected theorem induction_on₃ [s₃ : Setoid φ] {δ : Quotient s₁ → Quotient s₂ → Quotient s₃ → Prop} (q₁ : Quotient s₁)
    (q₂ : Quotient s₂) (q₃ : Quotient s₃) (h : ∀ a b c, δ ⟦a⟧ ⟦b⟧ ⟦c⟧) : δ q₁ q₂ q₃ :=
  Quotient.ind (fun a₁ => Quotient.ind (fun a₂ => Quotient.ind (fun a₃ => h a₁ a₂ a₃) q₃) q₂) q₁

end

section Exact

variable {α : Sort u}

variable [s : Setoid α]

include s

private def rel (q₁ q₂ : Quotient s) : Prop :=
  Quotient.liftOn₂ q₁ q₂ (fun a₁ a₂ => a₁ ≈ a₂) fun a₁ a₂ b₁ b₂ a₁b₁ a₂b₂ =>
    propext
      (Iff.intro (fun a₁a₂ => Setoid.trans (Setoid.symm a₁b₁) (Setoid.trans a₁a₂ a₂b₂)) fun b₁b₂ =>
        Setoid.trans a₁b₁ (Setoid.trans b₁b₂ (Setoid.symm a₂b₂)))

-- mathport name: «expr ~ »
local infixl:50 " ~ " => Rel

private theorem rel.refl : ∀ q : Quotient s, q ~ q := fun q => Quot.induction_on q fun a => Setoid.refl a

private theorem eq_imp_rel {q₁ q₂ : Quotient s} : q₁ = q₂ → q₁ ~ q₂ := fun h => Eq.recOn h (Rel.refl q₁)

theorem exact {a b : α} : ⟦a⟧ = ⟦b⟧ → a ≈ b := fun h => eq_imp_rel h

end Exact

section

universe u_a u_b u_c

variable {α : Sort u_a} {β : Sort u_b}

variable [s₁ : Setoid α] [s₂ : Setoid β]

include s₁ s₂

@[reducible, elab_as_elim]
protected def recOnSubsingleton₂ {φ : Quotient s₁ → Quotient s₂ → Sort u_c} [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)]
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  @Quotient.recOnSubsingleton _ s₁ (fun q => φ q q₂) (fun a => Quotient.ind (fun b => h a b) q₂) q₁ fun a =>
    Quotient.recOnSubsingleton q₂ fun b => f a b

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
  mk _ EqvGen.refl EqvGen.symm EqvGen.trans

def EqvGen.setoid : Setoid α :=
  Setoid.mk _ (EqvGen.is_equivalence r)

theorem Quot.exact {a b : α} (H : Quot.mk r a = Quot.mk r b) : EqvGen r a b :=
  @Quotient.exact _ (EqvGen.setoid r) a b
    (@congr_arg _ _ _ _ (Quot.lift (@Quotient.mk _ (EqvGen.setoid r)) fun x y h => Quot.sound (EqvGen.rel x y h)) H)

theorem Quot.eqv_gen_sound {r : α → α → Prop} {a b : α} (H : EqvGen r a b) : Quot.mk r a = Quot.mk r b :=
  EqvGen.rec_on H (fun x y h => Quot.sound h) (fun x => rfl) (fun x y _ IH => Eq.symm IH) fun x y z _ _ IH₁ IH₂ =>
    Eq.trans IH₁ IH₂

end

open Decidable

instance {α : Sort u} {s : Setoid α} [d : ∀ a b : α, Decidable (a ≈ b)] : DecidableEq (Quotient s) :=
  fun q₁ q₂ : Quotient s =>
  Quotient.recOnSubsingleton₂ q₁ q₂ fun a₁ a₂ =>
    match d a₁ a₂ with
    | is_true h₁ => isTrue (Quotient.sound h₁)
    | is_false h₂ => isFalse fun h => absurd (Quotient.exact h) h₂

