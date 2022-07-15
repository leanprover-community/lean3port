/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.Prod

universe u v

/-- A value `x : α` is accessible from `r` when every value that's lesser under `r` is also
accessible. Note that any value that's minimal under `r` is vacuously accessible.

Equivalently, `acc r x` when there is no infinite chain of elements starting at `x` that are related
under `r`.

This is used to state the definition of well-foundedness (see `well_founded`). -/
inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop
  | intro (x : α) (h : ∀ y, r y x → Acc y) : Acc x

namespace Acc

variable {α : Sort u} {r : α → α → Prop}

theorem invₓ {x y : α} (h₁ : Acc r x) (h₂ : r y x) : Acc r y :=
  Acc.recOnₓ h₁ (fun x₁ ac₁ ih h₂ => ac₁ y h₂) h₂

end Acc

/-- A relation `r : α → α → Prop` is well-founded when `∀ x, (∀ y, r y x → P y → P x) → P x` for all
predicates `P`. Equivalently, `acc r x` for all `x`.

Once you know that a relation is well_founded, you can use it to define fixpoint functions on `α`.-/
structure WellFounded {α : Sort u} (r : α → α → Prop) : Prop where intro ::
  apply : ∀ a, Acc r a

class HasWellFounded (α : Sort u) : Type u where
  R : α → α → Prop
  wf : WellFounded r

namespace WellFounded

section

parameter {α : Sort u}{r : α → α → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => r

parameter (hwf : WellFounded r)

def recursionₓ {C : α → Sort v} (a : α) (h : ∀ x, (∀ y, y≺x → C y) → C x) : C a :=
  Acc.recOnₓ (apply hwf a) fun x₁ ac₁ ih => h x₁ ih

theorem induction {C : α → Prop} (a : α) (h : ∀ x, (∀ y, y≺x → C y) → C x) : C a :=
  recursion a h

variable {C : α → Sort v}

variable (F : ∀ x, (∀ y, y≺x → C y) → C x)

def fixF (x : α) (a : Acc r x) : C x :=
  Acc.recOnₓ a fun x₁ ac₁ ih => F x₁ ih

theorem fix_F_eq (x : α) (acx : Acc r x) : fix_F F x acx = F x fun y : α p : y≺x => fix_F F y (Acc.invₓ acx p) :=
  Acc.drec (fun x r ih => rfl) acx

end

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

/-- Well-founded fixpoint -/
def fix (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  fixF F x (apply hwf x)

/-- Well-founded fixpoint satisfies fixpoint equation -/
theorem fix_eq (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) :
    fix hwf F x = F x fun y h => fix hwf F y :=
  fix_F_eq F x (apply hwf x)

end WellFounded

open WellFounded

/-- Empty relation is well-founded -/
theorem empty_wf {α : Sort u} : WellFounded (@EmptyRelation α) :=
  WellFounded.intro fun a : α => Acc.intro a fun b : α lt : False => False.ndrec _ lt

-- Subrelation of a well-founded relation is well-founded
namespace Subrelation

section

parameter {α : Sort u}{r Q : α → α → Prop}

parameter (h₁ : Subrelation Q r)

parameter (h₂ : WellFounded r)

theorem accessibleₓ {a : α} (ac : Acc r a) : Acc Q a :=
  Acc.recOnₓ ac fun x ax ih => Acc.intro x fun y : α lt : Q y x => ih y (h₁ lt)

theorem wfₓ : WellFounded Q :=
  ⟨fun a => accessible (apply h₂ a)⟩

end

end Subrelation

-- The inverse image of a well-founded relation is well-founded
namespace InvImage

section

parameter {α : Sort u}{β : Sort v}{r : β → β → Prop}

parameter (f : α → β)

parameter (h : WellFounded r)

private def acc_aux {b : β} (ac : Acc r b) : ∀ x : α, f x = b → Acc (InvImage r f) x :=
  Acc.recOnₓ ac fun x acx ih z e => Acc.intro z fun y lt => Eq.recOnₓ e (fun acx ih => ih (f y) lt y rfl) acx ih

theorem accessibleₓ {a : α} (ac : Acc r (f a)) : Acc (InvImage r f) a :=
  acc_aux ac a rfl

theorem wfₓ : WellFounded (InvImage r f) :=
  ⟨fun a => accessible (apply h (f a))⟩

end

end InvImage

/-- less-than is well-founded -/
theorem Nat.lt_wf : WellFounded Nat.Lt :=
  ⟨Nat.rec (Acc.intro 0 fun n h => absurd h (Nat.not_lt_zeroₓ n)) fun n ih =>
      Acc.intro (Nat.succ n) fun m h =>
        Or.elim (Nat.eq_or_lt_of_leₓ (Nat.le_of_succ_le_succₓ h)) (fun e => Eq.substr e ih) (Acc.invₓ ih)⟩

def Measureₓ {α : Sort u} : (α → ℕ) → α → α → Prop :=
  InvImage (· < ·)

theorem measure_wf {α : Sort u} (f : α → ℕ) : WellFounded (Measureₓ f) :=
  InvImage.wfₓ f Nat.lt_wf

def SizeofMeasure (α : Sort u) [SizeOf α] : α → α → Prop :=
  Measureₓ sizeof

theorem sizeof_measure_wf (α : Sort u) [SizeOf α] : WellFounded (SizeofMeasure α) :=
  measure_wf sizeof

instance hasWellFoundedOfHasSizeof (α : Sort u) [SizeOf α] : HasWellFounded α where
  R := SizeofMeasure α
  wf := sizeof_measure_wf α

namespace Prod

open WellFounded

section

variable {α : Type u} {β : Type v}

variable (ra : α → α → Prop)

variable (rb : β → β → Prop)

-- Lexicographical order based on ra and rb
inductive Lex : α × β → α × β → Prop
  | left {a₁} b₁ {a₂} b₂ (h : ra a₁ a₂) : lex (a₁, b₁) (a₂, b₂)
  | right a {b₁ b₂} (h : rb b₁ b₂) : lex (a, b₁) (a, b₂)

-- relational product based on ra and rb
inductive Rprod : α × β → α × β → Prop
  | intro {a₁ b₁ a₂ b₂} (h₁ : ra a₁ a₂) (h₂ : rb b₁ b₂) : rprod (a₁, b₁) (a₂, b₂)

end

section

parameter {α : Type u}{β : Type v}

parameter {ra : α → α → Prop}{rb : β → β → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => Lex ra rb

theorem lex_accessible {a} (aca : Acc ra a) (acb : ∀ b, Acc rb b) : ∀ b, Acc (Lex ra rb) (a, b) :=
  Acc.recOnₓ aca fun xa aca iha b =>
    Acc.recOnₓ (acb b) fun xb acb ihb =>
      Acc.intro (xa, xb) fun p lt =>
        have aux : xa = xa → xb = xb → Acc (Lex ra rb) p :=
          @Prod.Lex.rec_on α β ra rb (fun p₁ p₂ => fst p₂ = xa → snd p₂ = xb → Acc (Lex ra rb) p₁) p (xa, xb) lt
            (fun a₁ b₁ a₂ b₂ h eq₂ : a₂ = xa eq₃ : b₂ = xb => iha a₁ (Eq.recOnₓ eq₂ h) b₁)
            fun a b₁ b₂ h eq₂ : a = xa eq₃ : b₂ = xb => Eq.recOnₓ eq₂.symm (ihb b₁ (Eq.recOnₓ eq₃ h))
        aux rfl rfl

-- The lexicographical order of well founded relations is well-founded
theorem lex_wf (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Lex ra rb) :=
  ⟨fun p => casesOn p fun a b => lex_accessible (apply ha a) (WellFounded.apply hb) b⟩

-- relational product is a subrelation of the lex
theorem rprod_sub_lex : ∀ a b, Rprod ra rb a b → Lex ra rb a b := fun a b h =>
  Prod.Rprod.rec_on h fun a₁ b₁ a₂ b₂ h₁ h₂ => Lex.left b₁ b₂ h₁

-- The relational product of well founded relations is well-founded
theorem rprod_wf (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Rprod ra rb) :=
  Subrelation.wfₓ rprod_sub_lex (lex_wf ha hb)

end

instance hasWellFounded {α : Type u} {β : Type v} [s₁ : HasWellFounded α] [s₂ : HasWellFounded β] :
    HasWellFounded (α × β) where
  R := Lex s₁.R s₂.R
  wf := lex_wf s₁.wf s₂.wf

end Prod

