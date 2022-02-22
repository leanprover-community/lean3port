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

attribute [elab_as_eliminator] lift ind

protected theorem lift_beta {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) (c : ∀ a b, r a b → f a = f b)
    (a : α) : lift f c (Quot.mk r a) = f a :=
  rfl

protected theorem ind_beta {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (p : ∀ a, β (Quot.mk r a)) (a : α) :
    (ind p (Quot.mk r a) : β (Quot.mk r a)) = p a :=
  rfl

@[reducible, elab_as_eliminator]
protected def liftOn {α : Sort u} {β : Sort v} {r : α → α → Prop} (q : Quot r) (f : α → β)
    (c : ∀ a b, r a b → f a = f b) : β :=
  lift f c q

@[elab_as_eliminator]
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

protected theorem indep_coherent (f : ∀ a, β ⟦a⟧) (h : ∀ a b : α p : r a b, (Eq.ndrec (f a) (sound p) : β ⟦b⟧) = f b) :
    ∀ a b, r a b → Quot.indep f a = Quot.indep f b := fun a b e => PSigma.eq (sound e) (h a b e)

protected theorem lift_indep_pr1 (f : ∀ a, β ⟦a⟧) (h : ∀ a b : α p : r a b, (Eq.ndrec (f a) (sound p) : β ⟦b⟧) = f b)
    (q : Quot r) : (lift (Quot.indep f) (Quot.indep_coherent f h) q).1 = q :=
  Quot.ind (fun a : α => Eq.refl (Quot.indep f a).1) q

@[reducible, elab_as_eliminator]
protected def rec (f : ∀ a, β ⟦a⟧) (h : ∀ a b : α p : r a b, (Eq.ndrec (f a) (sound p) : β ⟦b⟧) = f b) (q : Quot r) :
    β q :=
  Eq.recOnₓ (Quot.lift_indep_pr1 f h q) (lift (Quot.indep f) (Quot.indep_coherent f h) q).2

@[reducible, elab_as_eliminator]
protected def recOn (q : Quot r) (f : ∀ a, β ⟦a⟧) (h : ∀ a b : α p : r a b, (Eq.ndrec (f a) (sound p) : β ⟦b⟧) = f b) :
    β q :=
  Quot.rec f h q

@[reducible, elab_as_eliminator]
protected def recOnSubsingleton [h : ∀ a, Subsingleton (β ⟦a⟧)] (q : Quot r) (f : ∀ a, β ⟦a⟧) : β q :=
  Quot.rec f (fun a b h => Subsingleton.elimₓ _ (f b)) q

@[reducible, elab_as_eliminator]
protected def hrecOn (q : Quot r) (f : ∀ a, β ⟦a⟧) (c : ∀ a b : α p : r a b, HEq (f a) (f b)) : β q :=
  Quot.recOn q f fun a b p =>
    eq_of_heq
      (calc
        HEq (Eq.ndrec (f a) (sound p) : β ⟦b⟧) (f a) := eq_rec_heqₓ (sound p) (f a)
        HEq _ (f b) := c a b p
        )

end

end Quot

def Quotientₓ {α : Sort u} (s : Setoidₓ α) :=
  @Quot α Setoidₓ.R

namespace Quotientₓ

protected def mk {α : Sort u} [s : Setoidₓ α] (a : α) : Quotientₓ s :=
  Quot.mk Setoidₓ.R a

-- mathport name: «expr⟦ ⟧»
notation:arg "⟦" a "⟧" => Quotientₓ.mk a

theorem sound {α : Sort u} [s : Setoidₓ α] {a b : α} : a ≈ b → ⟦a⟧ = ⟦b⟧ :=
  Quot.sound

@[reducible, elab_as_eliminator]
protected def lift {α : Sort u} {β : Sort v} [s : Setoidₓ α] (f : α → β) :
    (∀ a b, a ≈ b → f a = f b) → Quotientₓ s → β :=
  Quot.lift f

@[elab_as_eliminator]
protected theorem ind {α : Sort u} [s : Setoidₓ α] {β : Quotientₓ s → Prop} : (∀ a, β ⟦a⟧) → ∀ q, β q :=
  Quot.ind

@[reducible, elab_as_eliminator]
protected def liftOn {α : Sort u} {β : Sort v} [s : Setoidₓ α] (q : Quotientₓ s) (f : α → β)
    (c : ∀ a b, a ≈ b → f a = f b) : β :=
  Quot.liftOn q f c

@[elab_as_eliminator]
protected theorem induction_on {α : Sort u} [s : Setoidₓ α] {β : Quotientₓ s → Prop} (q : Quotientₓ s)
    (h : ∀ a, β ⟦a⟧) : β q :=
  Quot.induction_on q h

theorem exists_rep {α : Sort u} [s : Setoidₓ α] (q : Quotientₓ s) : ∃ a : α, ⟦a⟧ = q :=
  Quot.exists_rep q

section

variable {α : Sort u}

variable [s : Setoidₓ α]

variable {β : Quotientₓ s → Sort v}

protected def rec (f : ∀ a, β ⟦a⟧) (h : ∀ a b : α p : a ≈ b, (Eq.ndrec (f a) (Quotientₓ.sound p) : β ⟦b⟧) = f b)
    (q : Quotientₓ s) : β q :=
  Quot.rec f h q

@[reducible, elab_as_eliminator]
protected def recOn (q : Quotientₓ s) (f : ∀ a, β ⟦a⟧)
    (h : ∀ a b : α p : a ≈ b, (Eq.ndrec (f a) (Quotientₓ.sound p) : β ⟦b⟧) = f b) : β q :=
  Quot.recOn q f h

@[reducible, elab_as_eliminator]
protected def recOnSubsingleton [h : ∀ a, Subsingleton (β ⟦a⟧)] (q : Quotientₓ s) (f : ∀ a, β ⟦a⟧) : β q :=
  @Quot.recOnSubsingleton _ _ _ h q f

@[reducible, elab_as_eliminator]
protected def hrecOn (q : Quotientₓ s) (f : ∀ a, β ⟦a⟧) (c : ∀ a b : α p : a ≈ b, HEq (f a) (f b)) : β q :=
  Quot.hrecOn q f c

end

section

universe u_a u_b u_c

variable {α : Sort u_a} {β : Sort u_b} {φ : Sort u_c}

variable [s₁ : Setoidₓ α] [s₂ : Setoidₓ β]

include s₁ s₂

@[reducible, elab_as_eliminator]
protected def lift₂ (f : α → β → φ) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (q₁ : Quotientₓ s₁)
    (q₂ : Quotientₓ s₂) : φ :=
  Quotientₓ.lift (fun a₁ : α => Quotientₓ.lift (f a₁) (fun a b : β => c a₁ a a₁ b (Setoidₓ.refl a₁)) q₂)
    (fun h : a ≈ b =>
      @Quotientₓ.ind β s₂
        (fun a_1 : Quotientₓ s₂ =>
          Quotientₓ.lift (f a) (fun a_1 b : β => c a a_1 a b (Setoidₓ.refl a)) a_1 =
            Quotientₓ.lift (f b) (fun a b_1 : β => c b a b b_1 (Setoidₓ.refl b)) a_1)
        (fun a' : β => c a a' b a' h (Setoidₓ.refl a')) q₂)
    q₁

@[reducible, elab_as_eliminator]
protected def liftOn₂ (q₁ : Quotientₓ s₁) (q₂ : Quotientₓ s₂) (f : α → β → φ)
    (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : φ :=
  Quotientₓ.lift₂ f c q₁ q₂

@[elab_as_eliminator]
protected theorem ind₂ {φ : Quotientₓ s₁ → Quotientₓ s₂ → Prop} (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) (q₁ : Quotientₓ s₁)
    (q₂ : Quotientₓ s₂) : φ q₁ q₂ :=
  Quotientₓ.ind (fun a₁ => Quotientₓ.ind (fun a₂ => h a₁ a₂) q₂) q₁

@[elab_as_eliminator]
protected theorem induction_on₂ {φ : Quotientₓ s₁ → Quotientₓ s₂ → Prop} (q₁ : Quotientₓ s₁) (q₂ : Quotientₓ s₂)
    (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  Quotientₓ.ind (fun a₁ => Quotientₓ.ind (fun a₂ => h a₁ a₂) q₂) q₁

@[elab_as_eliminator]
protected theorem induction_on₃ [s₃ : Setoidₓ φ] {δ : Quotientₓ s₁ → Quotientₓ s₂ → Quotientₓ s₃ → Prop}
    (q₁ : Quotientₓ s₁) (q₂ : Quotientₓ s₂) (q₃ : Quotientₓ s₃) (h : ∀ a b c, δ ⟦a⟧ ⟦b⟧ ⟦c⟧) : δ q₁ q₂ q₃ :=
  Quotientₓ.ind (fun a₁ => Quotientₓ.ind (fun a₂ => Quotientₓ.ind (fun a₃ => h a₁ a₂ a₃) q₃) q₂) q₁

end

section Exact

variable {α : Sort u}

variable [s : Setoidₓ α]

include s

private def rel (q₁ q₂ : Quotientₓ s) : Prop :=
  Quotientₓ.liftOn₂ q₁ q₂ (fun a₁ a₂ => a₁ ≈ a₂) fun a₁ a₂ b₁ b₂ a₁b₁ a₂b₂ =>
    propext
      (Iff.intro (fun a₁a₂ => Setoidₓ.trans (Setoidₓ.symm a₁b₁) (Setoidₓ.trans a₁a₂ a₂b₂)) fun b₁b₂ =>
        Setoidₓ.trans a₁b₁ (Setoidₓ.trans b₁b₂ (Setoidₓ.symm a₂b₂)))

-- mathport name: «expr ~ »
local infixl:50 " ~ " => Rel

private theorem rel.refl : ∀ q : Quotientₓ s, q ~ q := fun q => Quot.induction_on q fun a => Setoidₓ.refl a

private theorem eq_imp_rel {q₁ q₂ : Quotientₓ s} : q₁ = q₂ → q₁ ~ q₂ := fun h => Eq.recOnₓ h (Rel.refl q₁)

theorem exact {a b : α} : ⟦a⟧ = ⟦b⟧ → a ≈ b := fun h => eq_imp_rel h

end Exact

section

universe u_a u_b u_c

variable {α : Sort u_a} {β : Sort u_b}

variable [s₁ : Setoidₓ α] [s₂ : Setoidₓ β]

include s₁ s₂

@[reducible, elab_as_eliminator]
protected def recOnSubsingleton₂ {φ : Quotientₓ s₁ → Quotientₓ s₂ → Sort u_c} [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)]
    (q₁ : Quotientₓ s₁) (q₂ : Quotientₓ s₂) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  @Quotientₓ.recOnSubsingleton _ s₁ (fun q => φ q q₂) (fun a => Quotientₓ.ind (fun b => h a b) q₂) q₁ fun a =>
    Quotientₓ.recOnSubsingleton q₂ fun b => f a b

end

end Quotientₓ

section

variable {α : Type u}

variable (r : α → α → Prop)

inductive EqvGen : α → α → Prop
  | rel : ∀ x y, r x y → EqvGen x y
  | refl : ∀ x, EqvGen x x
  | symm : ∀ x y, EqvGen x y → EqvGen y x
  | trans : ∀ x y z, EqvGen x y → EqvGen y z → EqvGen x z

theorem EqvGen.is_equivalence : Equivalenceₓ (@EqvGen α r) :=
  mk_equivalence _ EqvGen.refl EqvGen.symm EqvGen.trans

def EqvGen.setoid : Setoidₓ α :=
  Setoidₓ.mk _ (EqvGen.is_equivalence r)

theorem Quot.exact {a b : α} (H : Quot.mk r a = Quot.mk r b) : EqvGen r a b :=
  @Quotientₓ.exact _ (EqvGen.setoid r) a b
    (@congr_argₓ _ _ _ _ (Quot.lift (@Quotientₓ.mk _ (EqvGen.setoid r)) fun x y h => Quot.sound (EqvGen.rel x y h)) H)

theorem Quot.eqv_gen_sound {r : α → α → Prop} {a b : α} (H : EqvGen r a b) : Quot.mk r a = Quot.mk r b :=
  EqvGen.rec_on H (fun x y h => Quot.sound h) (fun x => rfl) (fun x y _ IH => Eq.symm IH) fun x y z _ _ IH₁ IH₂ =>
    Eq.trans IH₁ IH₂

end

open Decidable

instance {α : Sort u} {s : Setoidₓ α} [d : ∀ a b : α, Decidable (a ≈ b)] : DecidableEq (Quotientₓ s) :=
  fun q₁ q₂ : Quotientₓ s =>
  Quotientₓ.recOnSubsingleton₂ q₁ q₂ fun a₁ a₂ =>
    match d a₁ a₂ with
    | is_true h₁ => isTrue (Quotientₓ.sound h₁)
    | is_false h₂ => isFalse fun h => absurd (Quotientₓ.exact h) h₂

