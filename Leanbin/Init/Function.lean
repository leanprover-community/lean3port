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

#print Function.comp /-
/-- Composition of functions: `(f ∘ g) x = f (g x)`. -/
@[inline, reducible]
def comp (f : β → φ) (g : α → β) : α → φ := fun x => f (g x)
#align function.comp Function.comp
-/

/-- Composition of dependent functions: `(f ∘' g) x = f (g x)`, where type of `g x` depends on `x`
and type of `f (g x)` depends on `x` and `g x`. -/
@[inline, reducible]
def dcomp {β : α → Sort u₂} {φ : ∀ {x : α}, β x → Sort u₃} (f : ∀ {x : α} (y : β x), φ y) (g : ∀ x, β x) :
    ∀ x, φ (g x) := fun x => f (g x)
#align function.dcomp Function.dcomp

-- mathport name: «expr ∘ »
infixr:90 " ∘ " => Function.comp

-- mathport name: «expr ∘' »
infixr:80 " ∘' " => Function.dcomp

@[reducible]
def compRight (f : β → β → β) (g : α → β) : β → α → β := fun b a => f b (g a)
#align function.comp_right Function.compRight

@[reducible]
def compLeft (f : β → β → β) (g : α → β) : α → β → β := fun a b => f (g a) b
#align function.comp_left Function.compLeft

#print Function.onFun /-
/-- Given functions `f : β → β → φ` and `g : α → β`, produce a function `α → α → φ` that evaluates
`g` on each argument, then applies `f` to the results. Can be used, e.g., to transfer a relation
from `β` to `α`. -/
@[reducible]
def onFun (f : β → β → φ) (g : α → β) : α → α → φ := fun x y => f (g x) (g y)
#align function.on_fun Function.onFun
-/

#print Function.combine /-
@[reducible]
def combine (f : α → β → φ) (op : φ → δ → ζ) (g : α → β → δ) : α → β → ζ := fun x y => op (f x y) (g x y)
#align function.combine Function.combine
-/

#print Function.const /-
/-- Constant `λ _, a`. -/
@[reducible]
def const (β : Sort u₂) (a : α) : β → α := fun x => a
#align function.const Function.const
-/

#print Function.swap /-
@[reducible]
def swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y := fun y x => f x y
#align function.swap Function.swap
-/

#print Function.app /-
@[reducible]
def app {β : α → Sort u₂} (f : ∀ x, β x) (x : α) : β x :=
  f x
#align function.app Function.app
-/

-- mathport name: «expr on »
infixl:2 " on " => onFun

-- mathport name: «expr -[ ]- »
notation f " -[" op "]- " g => combine f op g

#print Function.left_id /-
theorem left_id (f : α → β) : id ∘ f = f :=
  rfl
#align function.left_id Function.left_id
-/

#print Function.right_id /-
theorem right_id (f : α → β) : f ∘ id = f :=
  rfl
#align function.right_id Function.right_id
-/

/- warning: function.comp_app -> Function.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u₁}} {β : Sort.{u₂}} {φ : Sort.{u₃}} (f : β -> φ) (g : α -> β) (a : α), Eq.{u₃} φ (Function.comp.{u₁ u₂ u₃} α β φ f g a) (f (g a))
but is expected to have type
  forall {β : Sort.{u_1}} {δ : Sort.{u_2}} {α : Sort.{u_3}} {f : β -> δ} {g : α -> β} {x : α}, Eq.{u_2} δ (Function.comp.{u_3 u_1 u_2} α β δ f g x) (f (g x))
Case conversion may be inaccurate. Consider using '#align function.comp_app Function.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : β → φ) (g : α → β) (a : α) : (f ∘ g) a = f (g a) :=
  rfl
#align function.comp_app Function.comp_apply

#print Function.comp.assoc /-
theorem comp.assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ g ∘ h :=
  rfl
#align function.comp.assoc Function.comp.assoc
-/

#print Function.comp.left_id /-
@[simp]
theorem comp.left_id (f : α → β) : id ∘ f = f :=
  rfl
#align function.comp.left_id Function.comp.left_id
-/

#print Function.comp.right_id /-
@[simp]
theorem comp.right_id (f : α → β) : f ∘ id = f :=
  rfl
#align function.comp.right_id Function.comp.right_id
-/

#print Function.comp_const_right /-
theorem comp_const_right (f : β → φ) (b : β) : f ∘ const α b = const α (f b) :=
  rfl
#align function.comp_const_right Function.comp_const_right
-/

#print Function.Injective /-
/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
#align function.injective Function.Injective
-/

#print Function.Injective.comp /-
theorem Injective.comp {g : β → φ} {f : α → β} (hg : Injective g) (hf : Injective f) : Injective (g ∘ f) := fun a₁ a₂ =>
  fun h => hf (hg h)
#align function.injective.comp Function.Injective.comp
-/

#print Function.Surjective /-
/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
@[reducible]
def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b
#align function.surjective Function.Surjective
-/

#print Function.Surjective.comp /-
theorem Surjective.comp {g : β → φ} {f : α → β} (hg : Surjective g) (hf : Surjective f) : Surjective (g ∘ f) :=
  fun c : φ =>
  Exists.elim (hg c) fun b hb =>
    Exists.elim (hf b) fun a ha => Exists.intro a (show g (f a) = c from Eq.trans (congr_arg g ha) hb)
#align function.surjective.comp Function.Surjective.comp
-/

#print Function.Bijective /-
/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f
#align function.bijective Function.Bijective
-/

#print Function.Bijective.comp /-
theorem Bijective.comp {g : β → φ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
  | ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩
#align function.bijective.comp Function.Bijective.comp
-/

#print Function.LeftInverse /-
/-- `left_inverse g f` means that g is a left inverse to f. That is, `g ∘ f = id`. -/
def LeftInverse (g : β → α) (f : α → β) : Prop :=
  ∀ x, g (f x) = x
#align function.left_inverse Function.LeftInverse
-/

#print Function.HasLeftInverse /-
/-- `has_left_inverse f` means that `f` has an unspecified left inverse. -/
def HasLeftInverse (f : α → β) : Prop :=
  ∃ finv : β → α, LeftInverse finv f
#align function.has_left_inverse Function.HasLeftInverse
-/

#print Function.RightInverse /-
/-- `right_inverse g f` means that g is a right inverse to f. That is, `f ∘ g = id`. -/
def RightInverse (g : β → α) (f : α → β) : Prop :=
  LeftInverse f g
#align function.right_inverse Function.RightInverse
-/

#print Function.HasRightInverse /-
/-- `has_right_inverse f` means that `f` has an unspecified right inverse. -/
def HasRightInverse (f : α → β) : Prop :=
  ∃ finv : β → α, RightInverse finv f
#align function.has_right_inverse Function.HasRightInverse
-/

#print Function.LeftInverse.injective /-
theorem LeftInverse.injective {g : β → α} {f : α → β} : LeftInverse g f → Injective f := fun h a b faeqfb =>
  calc
    a = g (f a) := (h a).symm
    _ = g (f b) := congr_arg g faeqfb
    _ = b := h b
    
#align function.left_inverse.injective Function.LeftInverse.injective
-/

#print Function.HasLeftInverse.injective /-
theorem HasLeftInverse.injective {f : α → β} : HasLeftInverse f → Injective f := fun h =>
  Exists.elim h fun finv inv => inv.Injective
#align function.has_left_inverse.injective Function.HasLeftInverse.injective
-/

#print Function.rightInverse_of_injective_of_leftInverse /-
theorem rightInverse_of_injective_of_leftInverse {f : α → β} {g : β → α} (injf : Injective f) (lfg : LeftInverse f g) :
    RightInverse f g := fun x =>
  have h : f (g (f x)) = f x := lfg (f x)
  injf h
#align function.right_inverse_of_injective_of_left_inverse Function.rightInverse_of_injective_of_leftInverse
-/

#print Function.RightInverse.surjective /-
theorem RightInverse.surjective {f : α → β} {g : β → α} (h : RightInverse g f) : Surjective f := fun y => ⟨g y, h y⟩
#align function.right_inverse.surjective Function.RightInverse.surjective
-/

#print Function.HasRightInverse.surjective /-
theorem HasRightInverse.surjective {f : α → β} : HasRightInverse f → Surjective f
  | ⟨finv, inv⟩ => inv.Surjective
#align function.has_right_inverse.surjective Function.HasRightInverse.surjective
-/

#print Function.leftInverse_of_surjective_of_rightInverse /-
theorem leftInverse_of_surjective_of_rightInverse {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  Exists.elim (surjf y) fun x hx =>
    calc
      f (g y) = f (g (f x)) := hx ▸ rfl
      _ = f x := Eq.symm (rfg x) ▸ rfl
      _ = y := hx
      
#align function.left_inverse_of_surjective_of_right_inverse Function.leftInverse_of_surjective_of_rightInverse
-/

#print Function.injective_id /-
theorem injective_id : Injective (@id α) := fun a₁ a₂ h => h
#align function.injective_id Function.injective_id
-/

#print Function.surjective_id /-
theorem surjective_id : Surjective (@id α) := fun a => ⟨a, rfl⟩
#align function.surjective_id Function.surjective_id
-/

#print Function.bijective_id /-
theorem bijective_id : Bijective (@id α) :=
  ⟨injective_id, surjective_id⟩
#align function.bijective_id Function.bijective_id
-/

end Function

namespace Function

variable {α : Type u₁} {β : Type u₂} {φ : Type u₃}

#print Function.curry /-
/-- Interpret a function on `α × β` as a function with two arguments. -/
@[inline]
def curry : (α × β → φ) → α → β → φ := fun f a b => f (a, b)
#align function.curry Function.curry
-/

#print Function.uncurry /-
/-- Interpret a function with two arguments as a function on `α × β` -/
@[inline]
def uncurry : (α → β → φ) → α × β → φ := fun f a => f a.1 a.2
#align function.uncurry Function.uncurry
-/

#print Function.curry_uncurry /-
@[simp]
theorem curry_uncurry (f : α → β → φ) : curry (uncurry f) = f :=
  rfl
#align function.curry_uncurry Function.curry_uncurry
-/

#print Function.uncurry_curry /-
@[simp]
theorem uncurry_curry (f : α × β → φ) : uncurry (curry f) = f :=
  funext fun ⟨a, b⟩ => rfl
#align function.uncurry_curry Function.uncurry_curry
-/

#print Function.LeftInverse.id /-
protected theorem LeftInverse.id {g : β → α} {f : α → β} (h : LeftInverse g f) : g ∘ f = id :=
  funext h
#align function.left_inverse.id Function.LeftInverse.id
-/

#print Function.RightInverse.id /-
protected theorem RightInverse.id {g : β → α} {f : α → β} (h : RightInverse g f) : f ∘ g = id :=
  funext h
#align function.right_inverse.id Function.RightInverse.id
-/

end Function

