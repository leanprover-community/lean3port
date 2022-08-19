/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.Prod

universe u v

class HasWellFounded (α : Sort u) : Type u where
  R : α → α → Prop
  wf : WellFounded R

namespace WellFounded

section

variable {α : Sort u} {r : α → α → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => r

variable (hwf : WellFounded r)

variable {C : α → Sort v}

variable (F : ∀ x, (∀ y, y≺x → C y) → C x)

theorem fix_F_eq (x : α) (acx : Acc r x) : fixF F x acx = F x fun (y : α) (p : y≺x) => fixF F y (Acc.inv acx p) :=
  Acc.rec (fun x r ih => rfl) acx

end

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

end WellFounded

open WellFounded

/-- Empty relation is well-founded -/
theorem empty_wf {α : Sort u} : WellFounded (@EmptyRelation α) :=
  WellFounded.intro fun a : α => Acc.intro a fun (b : α) (lt : False) => False.rec lt

/-- less-than is well-founded -/
theorem Nat.lt_wf : WellFounded (fun m n : Nat => m < n) :=
  ⟨Nat.rec (Acc.intro 0 fun n h => absurd h (Nat.not_lt_zero n)) fun n ih =>
      Acc.intro (Nat.succ n) fun m h =>
        Or.elim (Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h)) (fun e => Eq.substr e ih) (Acc.inv ih)⟩

theorem measure_wf {α : Sort u} (f : α → ℕ) : WellFounded (Measure f) :=
  InvImage.wf f Nat.lt_wf

def SizeofMeasure (α : Sort u) [SizeOf α] : α → α → Prop :=
  Measure sizeOf

theorem sizeof_measure_wf (α : Sort u) [SizeOf α] : WellFounded (SizeofMeasure α) :=
  measure_wf sizeOf

instance hasWellFoundedOfHasSizeof (α : Sort u) [SizeOf α] : HasWellFounded α where
  R := SizeofMeasure α
  wf := sizeof_measure_wf α

namespace Prod

open WellFounded

section

variable {α : Type u} {β : Type v}

variable (ra : α → α → Prop)

variable (rb : β → β → Prop)

-- relational product based on ra and rb
inductive Rprod : α × β → α × β → Prop
  | intro {a₁ b₁ a₂ b₂} (h₁ : ra a₁ a₂) (h₂ : rb b₁ b₂) : Rprod (a₁, b₁) (a₂, b₂)

end

section

variable {α : Type u}{β : Type v}

variable {ra : α → α → Prop}{rb : β → β → Prop}

def lex_accessible (aca : Acc ra a) (acb : (b : β) → Acc rb b) (b : β) : Acc (Lex ra rb) (a, b) := by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction (acb b) with
    | intro xb _ ihb =>
      apply Acc.intro (_, xb)
      intro p lt
      cases lt with
      | left  _ _ h => apply iha _ h
      | right _ h   => apply ihb _ h

-- The lexicographical order of well founded relations is well-founded
theorem lex_wf (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Lex ra rb) :=
  ⟨fun ⟨a, b⟩ => lex_accessible (apply ha a) (WellFounded.apply hb) b⟩

-- relational product is a subrelation of the lex
theorem rprod_sub_lex : ∀ a b, Rprod ra rb a b → Lex ra rb a b := fun a b h =>
  Prod.Rprod.recOn h @fun a₁ b₁ a₂ b₂ h₁ h₂ => Lex.left b₁ b₂ h₁

-- The relational product of well founded relations is well-founded
theorem rprod_wf (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Rprod ra rb) :=
  Subrelation.wf (rprod_sub_lex _ _) (lex_wf ha hb)

end

instance hasWellFounded {α : Type u} {β : Type v} [s₁ : HasWellFounded α] [s₂ : HasWellFounded β] :
    HasWellFounded (α × β) where
  R := Lex s₁.R s₂.R
  wf := lex_wf s₁.wf s₂.wf

end Prod

