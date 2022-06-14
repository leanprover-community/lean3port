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


universe u₁ u₂ u₃ u₄

namespace Function

variable {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₁}

/-- Composition of functions: `(f ∘ g) x = f (g x)`. -/
@[inline, reducible]
def comp (f : β → φ) (g : α → β) : α → φ := fun x => f (g x)

/-- Composition of dependent functions: `(f ∘' g) x = f (g x)`, where type of `g x` depends on `x`
and type of `f (g x)` depends on `x` and `g x`. -/
@[inline, reducible]
def dcomp {β : α → Sort u₂} {φ : ∀ {x : α}, β x → Sort u₃} (f : ∀ {x : α} y : β x, φ y) (g : ∀ x, β x) : ∀ x, φ (g x) :=
  fun x => f (g x)

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

@[reducible]
def combine (f : α → β → φ) (op : φ → δ → ζ) (g : α → β → δ) : α → β → ζ := fun x y => op (f x y) (g x y)

/-- Constant `λ _, a`. -/
@[reducible]
def const (β : Sort u₂) (a : α) : β → α := fun x => a

@[reducible]
def swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y := fun y x => f x y

@[reducible]
def app {β : α → Sort u₂} (f : ∀ x, β x) (x : α) : β x :=
  f x

-- mathport name: «expr on »
infixl:2 " on " => onFun

-- mathport name: «expr -[ ]- »
notation f " -[" op "]- " g => combine f op g

theorem left_id (f : α → β) : id ∘ f = f :=
  rfl

theorem right_id (f : α → β) : f ∘ id = f :=
  rfl

@[simp]
theorem comp_app (f : β → φ) (g : α → β) (a : α) : (f ∘ g) a = f (g a) :=
  rfl

theorem comp.assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ g ∘ h :=
  rfl

@[simp]
theorem comp.left_id (f : α → β) : id ∘ f = f :=
  rfl

@[simp]
theorem comp.right_id (f : α → β) : f ∘ id = f :=
  rfl

theorem comp_const_right (f : β → φ) (b : β) : f ∘ const α b = const α (f b) :=
  rfl

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

theorem Injective.comp {g : β → φ} {f : α → β} (hg : Injective g) (hf : Injective f) : Injective (g ∘ f) := fun a₁ a₂ =>
  fun h => hf (hg h)

/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
@[reducible]
def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

theorem Surjective.comp {g : β → φ} {f : α → β} (hg : Surjective g) (hf : Surjective f) : Surjective (g ∘ f) :=
  fun c : φ =>
  Exists.elim (hg c) fun b hb =>
    Exists.elim (hf b) fun a ha => Exists.introₓ a (show g (f a) = c from Eq.trans (congr_arg g ha) hb)

/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f

theorem Bijective.comp {g : β → φ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
  | ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩

/-- `left_inverse g f` means that g is a left inverse to f. That is, `g ∘ f = id`. -/
def LeftInverse (g : β → α) (f : α → β) : Prop :=
  ∀ x, g (f x) = x

/-- `has_left_inverse f` means that `f` has an unspecified left inverse. -/
def HasLeftInverse (f : α → β) : Prop :=
  ∃ finv : β → α, LeftInverse finv f

/-- `right_inverse g f` means that g is a right inverse to f. That is, `f ∘ g = id`. -/
def RightInverse (g : β → α) (f : α → β) : Prop :=
  LeftInverse f g

/-- `has_right_inverse f` means that `f` has an unspecified right inverse. -/
def HasRightInverse (f : α → β) : Prop :=
  ∃ finv : β → α, RightInverse finv f

theorem LeftInverse.injective {g : β → α} {f : α → β} : LeftInverse g f → Injective f := fun h a b faeqfb =>
  calc
    a = g (f a) := (h a).symm
    _ = g (f b) := congr_arg g faeqfb
    _ = b := h b
    

theorem HasLeftInverse.injective {f : α → β} : HasLeftInverse f → Injective f := fun h =>
  Exists.elim h fun finv inv => inv.Injective

theorem right_inverse_of_injective_of_left_inverse {f : α → β} {g : β → α} (injf : Injective f)
    (lfg : LeftInverse f g) : RightInverse f g := fun x =>
  have h : f (g (f x)) = f x := lfg (f x)
  injf h

theorem RightInverse.surjective {f : α → β} {g : β → α} (h : RightInverse g f) : Surjective f := fun y => ⟨g y, h y⟩

theorem HasRightInverse.surjective {f : α → β} : HasRightInverse f → Surjective f
  | ⟨finv, inv⟩ => inv.Surjective

theorem left_inverse_of_surjective_of_right_inverse {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  Exists.elim (surjf y) fun x hx =>
    calc
      f (g y) = f (g (f x)) := hx ▸ rfl
      _ = f x := Eq.symm (rfg x) ▸ rfl
      _ = y := hx
      

theorem injective_id : Injective (@id α) := fun a₁ a₂ h => h

theorem surjective_id : Surjective (@id α) := fun a => ⟨a, rfl⟩

theorem bijective_id : Bijective (@id α) :=
  ⟨injective_id, surjective_id⟩

end Function

namespace Function

variable {α : Type u₁} {β : Type u₂} {φ : Type u₃}

/-- Interpret a function on `α × β` as a function with two arguments. -/
@[inline]
def curry : (α × β → φ) → α → β → φ := fun f a b => f (a, b)

/-- Interpret a function with two arguments as a function on `α × β` -/
@[inline]
def uncurry : (α → β → φ) → α × β → φ := fun f a => f a.1 a.2

@[simp]
theorem curry_uncurry (f : α → β → φ) : curry (uncurry f) = f :=
  rfl

@[simp]
theorem uncurry_curry (f : α × β → φ) : uncurry (curry f) = f :=
  funext fun ⟨a, b⟩ => rfl

protected theorem LeftInverse.id {g : β → α} {f : α → β} (h : LeftInverse g f) : g ∘ f = id :=
  funext h

protected theorem RightInverse.id {g : β → α} {f : α → β} (h : RightInverse g f) : f ∘ g = id :=
  funext h

end Function

