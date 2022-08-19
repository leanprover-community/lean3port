/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Haitao Zhang
-/
prelude
import Leanbin.Init.Data.Prod
import Leanbin.Init.Funext
import Leanbin.Init.Logic

/-!
# General operations on functions
-/

namespace Function

/-- Composition of dependent functions: `(f ∘' g) x = f (g x)`, where type of `g x` depends on `x`
and type of `f (g x)` depends on `x` and `g x`. -/
@[inline, reducible]
def dcomp {β : α → Sort u₂} {φ : ∀ {x : α}, β x → Sort u₃} (f : ∀ {x : α} (y : β x), φ y) (g : ∀ x, β x) :
    ∀ x, φ (g x) := fun x => f (g x)

-- mathport name: «expr ∘' »
infixr:80 " ∘' " => Function.dcomp

@[reducible]
def compRight (f : β → β → β) (g : α → β) : β → α → β := fun b a => f b (g a)

@[reducible]
def compLeft (f : β → β → β) (g : α → β) : α → β → β := fun a b => f (g a) b

/-- Given functions `f : β → β → φ` and `g : α → β`, produce a function `α → α → φ` that evaluates
`g` on each argument, then applies `f` to the results. Can be used, e.g., to transfer a relation
from `β` to `α`. -/
@[reducible]
def onFun (f : β → β → φ) (g : α → β) : α → α → φ := fun x y => f (g x) (g y)

-- mathport name: «expr on »
infixl:2 " on " => onFun

-- mathport name: «expr -[ ]- »
notation f " -[" op "]- " g => combine f op g

@[simp]
theorem comp_app (f : β → φ) (g : α → β) (a : α) : (f ∘ g) a = f (g a) :=
  rfl

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
abbrev Injective (f : α → β) : Prop :=
  f.injective

theorem Injective.comp {g : β → φ} {f : α → β} (hg : Injective g) (hf : Injective f) : Injective (g ∘ f) := fun a₁ a₂ =>
  fun h => hf (hg h)

/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
@[reducible]
def Surjective (f : α → β) : Prop :=
  f.surjective

theorem Surjective.comp {g : β → φ} {f : α → β} (hg : Surjective g) (hf : Surjective f) : Surjective (g ∘ f) :=
  fun c : φ =>
  Exists.elim (hg c) fun b hb =>
    Exists.elim (hf b) fun a ha => Exists.intro a (show g (f a) = c from Eq.trans (congr_arg g ha) hb)

/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f

theorem Bijective.comp {g : β → φ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
  | ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩

/-- `has_left_inverse f` means that `f` has an unspecified left inverse. -/
def HasLeftInverse (f : α → β) : Prop :=
  ∃ finv : β → α, LeftInverse finv f

/-- `has_right_inverse f` means that `f` has an unspecified right inverse. -/
def HasRightInverse (f : α → β) : Prop :=
  ∃ finv : β → α, RightInverse finv f

theorem HasLeftInverse.injective {f : α → β} : HasLeftInverse f → Injective f := fun h =>
  Exists.elim h fun finv inv => inv.injective

theorem right_inverse_of_injective_of_left_inverse {f : α → β} {g : β → α} (injf : Injective f)
    (lfg : LeftInverse f g) : RightInverse f g := fun x =>
  have h : f (g (f x)) = f x := lfg (f x)
  injf h

theorem HasRightInverse.surjective {f : α → β} : HasRightInverse f → Surjective f
  | ⟨finv, inv⟩ => inv.surjective

theorem left_inverse_of_surjective_of_right_inverse {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  Exists.elim (surjf y) fun x hx =>
    calc
      f (g y) = f (g (f x)) := hx ▸ rfl
      _ = f x := Eq.symm (rfg x) ▸ rfl
      _ = y := hx

end Function
