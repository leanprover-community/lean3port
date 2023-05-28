/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.wf
! leanprover-community/lean commit 4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.Prod

universe u v

#print Acc /-
/-- A value `x : α` is accessible from `r` when every value that's lesser under `r` is also
accessible. Note that any value that's minimal under `r` is vacuously accessible.

Equivalently, `acc r x` when there is no infinite chain of elements starting at `x` that are related
under `r`.

This is used to state the definition of well-foundedness (see `well_founded`). -/
inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop
  | intro (x : α) (h : ∀ y, r y x → Acc y) : Acc x
#align acc Acc
-/

namespace Acc

variable {α : Sort u} {r : α → α → Prop}

#print Acc.inv /-
theorem inv {x y : α} (h₁ : Acc r x) (h₂ : r y x) : Acc r y :=
  Acc.recOn h₁ (fun x₁ ac₁ ih h₂ => ac₁ y h₂) h₂
#align acc.inv Acc.inv
-/

end Acc

#print WellFounded /-
/-- A relation `r : α → α → Prop` is well-founded when `∀ x, (∀ y, r y x → P y → P x) → P x` for all
predicates `P`. Equivalently, `acc r x` for all `x`.

Once you know that a relation is well_founded, you can use it to define fixpoint functions on `α`.-/
structure WellFounded {α : Sort u} (r : α → α → Prop) : Prop where intro ::
  apply : ∀ a, Acc r a
#align well_founded WellFounded
-/

class WellFoundedRelation (α : Sort u) : Type u where
  R : α → α → Prop
  wf : WellFounded r
#align has_well_founded WellFoundedRelation

namespace WellFounded

section

parameter {α : Sort u}{r : α → α → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => r

parameter (hwf : WellFounded r)

#print WellFounded.recursion /-
def recursion {C : α → Sort v} (a : α) (h : ∀ x, (∀ y, y≺x → C y) → C x) : C a :=
  Acc.recOn (apply hwf a) fun x₁ ac₁ ih => h x₁ ih
#align well_founded.recursion WellFounded.recursion
-/

#print WellFounded.induction /-
theorem induction {C : α → Prop} (a : α) (h : ∀ x, (∀ y, y≺x → C y) → C x) : C a :=
  recursion a h
#align well_founded.induction WellFounded.induction
-/

variable {C : α → Sort v}

variable (F : ∀ x, (∀ y, y≺x → C y) → C x)

#print WellFounded.fixF /-
def fixF (x : α) (a : Acc r x) : C x :=
  Acc.recOn a fun x₁ ac₁ ih => F x₁ ih
#align well_founded.fix_F WellFounded.fixF
-/

theorem fixF_eq (x : α) (acx : Acc r x) :
    fix_F F x acx = F x fun (y : α) (p : y≺x) => fix_F F y (Acc.inv acx p) :=
  Acc.drec (fun x r ih => rfl) acx
#align well_founded.fix_F_eq WellFounded.fixF_eq

end

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

#print WellFounded.fix /-
/-- Well-founded fixpoint -/
def fix (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  fixF F x (apply hwf x)
#align well_founded.fix WellFounded.fix
-/

#print WellFounded.fix_eq /-
/-- Well-founded fixpoint satisfies fixpoint equation -/
theorem fix_eq (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) :
    fix hwf F x = F x fun y h => fix hwf F y :=
  fixF_eq F x (apply hwf x)
#align well_founded.fix_eq WellFounded.fix_eq
-/

end WellFounded

open WellFounded

/-- Empty relation is well-founded -/
theorem empty_wf {α : Sort u} : WellFounded (@EmptyRelation α) :=
  WellFounded.intro fun a : α => Acc.intro a fun (b : α) (lt : False) => False.ndrec _ lt
#align empty_wf empty_wf

/-! Subrelation of a well-founded relation is well-founded -/


namespace Subrelation

section

parameter {α : Sort u}{r Q : α → α → Prop}

parameter (h₁ : Subrelation Q r)

parameter (h₂ : WellFounded r)

theorem accessible {a : α} (ac : Acc r a) : Acc Q a :=
  Acc.recOn ac fun x ax ih => Acc.intro x fun (y : α) (lt : Q y x) => ih y (h₁ lt)
#align subrelation.accessible Subrelation.accessibleₓ

#print Subrelation.wf /-
theorem wf : WellFounded Q :=
  ⟨fun a => accessible (apply h₂ a)⟩
#align subrelation.wf Subrelation.wf
-/

end

end Subrelation

-- The inverse image of a well-founded relation is well-founded
namespace InvImage

section

parameter {α : Sort u}{β : Sort v}{r : β → β → Prop}

parameter (f : α → β)

parameter (h : WellFounded r)

private def acc_aux {b : β} (ac : Acc r b) : ∀ x : α, f x = b → Acc (InvImage r f) x :=
  Acc.recOn ac fun x acx ih z e =>
    Acc.intro z fun y lt => Eq.recOn e (fun acx ih => ih (f y) lt y rfl) acx ih

theorem accessible {a : α} (ac : Acc r (f a)) : Acc (InvImage r f) a :=
  acc_aux ac a rfl
#align inv_image.accessible InvImage.accessibleₓ

#print InvImage.wf /-
theorem wf : WellFounded (InvImage r f) :=
  ⟨fun a => accessible (apply h (f a))⟩
#align inv_image.wf InvImage.wf
-/

end

end InvImage

/-- less-than is well-founded -/
theorem Nat.lt_wfRel : WellFounded Nat.lt :=
  ⟨Nat.rec (Acc.intro 0 fun n h => absurd h (Nat.not_lt_zero n)) fun n ih =>
      Acc.intro (Nat.succ n) fun m h =>
        Or.elim (Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h)) (fun e => Eq.substr e ih)
          (Acc.inv ih)⟩
#align nat.lt_wf Nat.lt_wfRel

#print Measure /-
def Measure {α : Sort u} : (α → ℕ) → α → α → Prop :=
  InvImage (· < ·)
#align measure Measure
-/

theorem measure_wf {α : Sort u} (f : α → ℕ) : WellFounded (Measure f) :=
  InvImage.wf f Nat.lt_wfRel
#align measure_wf measure_wf

def SizeofMeasure (α : Sort u) [SizeOf α] : α → α → Prop :=
  Measure SizeOf.sizeOf
#align sizeof_measure SizeofMeasure

theorem sizeofMeasure_wf (α : Sort u) [SizeOf α] : WellFounded (SizeofMeasure α) :=
  measure_wf SizeOf.sizeOf
#align sizeof_measure_wf sizeofMeasure_wf

instance hasWellFoundedOfHasSizeof (α : Sort u) [SizeOf α] : WellFoundedRelation α
    where
  R := SizeofMeasure α
  wf := sizeofMeasure_wf α
#align has_well_founded_of_has_sizeof hasWellFoundedOfHasSizeof

namespace Prod

open WellFounded

section

variable {α : Type u} {β : Type v}

variable (ra : α → α → Prop)

variable (rb : β → β → Prop)

#print Prod.Lex /-
-- Lexicographical order based on ra and rb
inductive Lex : α × β → α × β → Prop
  | left {a₁} (b₁) {a₂} (b₂) (h : ra a₁ a₂) : Lex (a₁, b₁) (a₂, b₂)
  | right (a) {b₁ b₂} (h : rb b₁ b₂) : Lex (a, b₁) (a, b₂)
#align prod.lex Prod.Lex
-/

#print Prod.RProd /-
-- relational product based on ra and rb
inductive RProd : α × β → α × β → Prop
  | intro {a₁ b₁ a₂ b₂} (h₁ : ra a₁ a₂) (h₂ : rb b₁ b₂) : rprod (a₁, b₁) (a₂, b₂)
#align prod.rprod Prod.RProd
-/

end

section

parameter {α : Type u}{β : Type v}

parameter {ra : α → α → Prop}{rb : β → β → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => Lex ra rb

theorem lex_accessible {a} (aca : Acc ra a) (acb : ∀ b, Acc rb b) : ∀ b, Acc (Lex ra rb) (a, b) :=
  Acc.recOn aca fun xa aca iha b =>
    Acc.recOn (acb b) fun xb acb ihb =>
      Acc.intro (xa, xb) fun p lt =>
        have aux : xa = xa → xb = xb → Acc (Lex ra rb) p :=
          @Prod.Lex.rec_on α β ra rb (fun p₁ p₂ => fst p₂ = xa → snd p₂ = xb → Acc (Lex ra rb) p₁) p
            (xa, xb) lt
            (fun a₁ b₁ a₂ b₂ h (eq₂ : a₂ = xa) (eq₃ : b₂ = xb) => iha a₁ (Eq.recOn eq₂ h) b₁)
            fun a b₁ b₂ h (eq₂ : a = xa) (eq₃ : b₂ = xb) =>
            Eq.recOn eq₂.symm (ihb b₁ (Eq.recOn eq₃ h))
        aux rfl rfl
#align prod.lex_accessible Prod.lex_accessible

#print WellFounded.prod_lex /-
-- The lexicographical order of well founded relations is well-founded
theorem prod_lex (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Lex ra rb) :=
  ⟨fun p => casesOn p fun a b => lex_accessible (apply ha a) (WellFounded.apply hb) b⟩
#align prod.lex_wf WellFounded.prod_lex
-/

-- relational product is a subrelation of the lex
theorem rProd_sub_lex : ∀ a b, RProd ra rb a b → Lex ra rb a b := fun a b h =>
  Prod.RProd.rec_on h fun a₁ b₁ a₂ b₂ h₁ h₂ => Lex.left b₁ b₂ h₁
#align prod.rprod_sub_lex Prod.rProd_sub_lex

-- The relational product of well founded relations is well-founded
theorem rProd_wf (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (RProd ra rb) :=
  Subrelation.wf rprod_sub_lex (lex_wf ha hb)
#align prod.rprod_wf Prod.rProd_wf

end

instance hasWellFounded {α : Type u} {β : Type v} [s₁ : WellFoundedRelation α]
    [s₂ : WellFoundedRelation β] : WellFoundedRelation (α × β)
    where
  R := Lex s₁.R s₂.R
  wf := prod_lex s₁.wf s₂.wf
#align prod.has_well_founded Prod.hasWellFounded

end Prod

