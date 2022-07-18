/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Sigma.Basic
import Leanbin.Init.Meta.Default

universe u v

namespace PSigma

section

variable {α : Sort u} {β : α → Sort v}

variable (r : α → α → Prop)

variable (s : ∀ a, β a → β a → Prop)

-- Lexicographical order based on r and s
inductive Lex : PSigma β → PSigma β → Prop
  | left : ∀ {a₁ : α} (b₁ : β a₁) {a₂ : α} (b₂ : β a₂), r a₁ a₂ → lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  | right : ∀ (a : α) {b₁ b₂ : β a}, s a b₁ b₂ → lex ⟨a, b₁⟩ ⟨a, b₂⟩

end

section

open WellFounded Tactic

parameter {α : Sort u}{β : α → Sort v}

parameter {r : α → α → Prop}{s : ∀ a : α, β a → β a → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => Lex r s

theorem lex_accessible {a} (aca : Acc r a) (acb : ∀ a, WellFounded (s a)) : ∀ b : β a, Acc (Lex r s) ⟨a, b⟩ :=
  Acc.recOnₓ aca fun xa aca (iha : ∀ y, r y xa → ∀ b : β y, Acc (Lex r s) ⟨y, b⟩) => fun b : β xa =>
    Acc.recOnₓ (WellFounded.apply (acb xa) b) fun xb acb (ihb : ∀ y : β xa, s xa y xb → Acc (Lex r s) ⟨xa, y⟩) =>
      Acc.intro ⟨xa, xb⟩ fun p (lt : p≺⟨xa, xb⟩) =>
        have aux : xa = xa → HEq xb xb → Acc (Lex r s) p :=
          @PSigma.Lex.rec_on α β r s (fun p₁ p₂ => p₂.1 = xa → HEq p₂.2 xb → Acc (Lex r s) p₁) p ⟨xa, xb⟩ lt
            (fun (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) (h : r a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : HEq b₂ xb) => by
              subst eq₂
              exact iha a₁ h b₁)
            fun (a : α) (b₁ b₂ : β a) (h : s a b₁ b₂) (eq₂ : a = xa) (eq₃ : HEq b₂ xb) => by
            subst eq₂
            have new_eq₃ := eq_of_heq eq₃
            subst new_eq₃
            exact ihb b₁ h
        aux rfl (HEq.refl xb)

-- The lexicographical order of well founded relations is well-founded
theorem lex_wf (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lex_accessible (WellFounded.apply ha a) hb b

end

section

parameter {α : Sort u}{β : Sort v}

def LexNdep (r : α → α → Prop) (s : β → β → Prop) :=
  Lex r fun a : α => s

theorem lex_ndep_wf {r : α → α → Prop} {s : β → β → Prop} (ha : WellFounded r) (hb : WellFounded s) :
    WellFounded (lex_ndep r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lex_accessible (WellFounded.apply ha a) (fun x => hb) b

end

section

variable {α : Sort u} {β : Sort v}

variable (r : α → α → Prop)

variable (s : β → β → Prop)

-- Reverse lexicographical order based on r and s
inductive RevLex : (@PSigma α fun a => β) → (@PSigma α fun a => β) → Prop
  | left : ∀ {a₁ a₂ : α} (b : β), r a₁ a₂ → rev_lex ⟨a₁, b⟩ ⟨a₂, b⟩
  | right : ∀ (a₁ : α) {b₁ : β} (a₂ : α) {b₂ : β}, s b₁ b₂ → rev_lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩

end

section

open WellFounded Tactic

parameter {α : Sort u}{β : Sort v}

parameter {r : α → α → Prop}{s : β → β → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => RevLex r s

theorem rev_lex_accessible {b} (acb : Acc s b) (aca : ∀ a, Acc r a) : ∀ a, Acc (RevLex r s) ⟨a, b⟩ :=
  Acc.recOnₓ acb fun xb acb (ihb : ∀ y, s y xb → ∀ a, Acc (RevLex r s) ⟨a, y⟩) => fun a =>
    Acc.recOnₓ (aca a) fun xa aca (iha : ∀ y, r y xa → Acc (RevLex r s) (mk y xb)) =>
      Acc.intro ⟨xa, xb⟩ fun p (lt : p≺⟨xa, xb⟩) =>
        have aux : xa = xa → xb = xb → Acc (RevLex r s) p :=
          @RevLex.rec_on α β r s (fun p₁ p₂ => fst p₂ = xa → snd p₂ = xb → Acc (RevLex r s) p₁) p ⟨xa, xb⟩ lt
            (fun a₁ a₂ b (h : r a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b = xb) =>
              show Acc (RevLex r s) ⟨a₁, b⟩ from
                have r₁ : r a₁ xa := Eq.recOnₓ eq₂ h
                have aux : Acc (RevLex r s) ⟨a₁, xb⟩ := iha a₁ r₁
                Eq.recOnₓ (Eq.symm eq₃) aux)
            fun a₁ b₁ a₂ b₂ (h : s b₁ b₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb) =>
            show Acc (RevLex r s) (mk a₁ b₁) from
              have s₁ : s b₁ xb := Eq.recOnₓ eq₃ h
              ihb b₁ s₁ a₁
        aux rfl rfl

theorem rev_lex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => rev_lex_accessible (apply hb b) (WellFounded.apply ha) a

end

section

def SkipLeft (α : Type u) {β : Type v} (s : β → β → Prop) : (@PSigma α fun a => β) → (@PSigma α fun a => β) → Prop :=
  RevLex EmptyRelation s

theorem skip_left_wf (α : Type u) {β : Type v} {s : β → β → Prop} (hb : WellFounded s) : WellFounded (SkipLeft α s) :=
  rev_lex_wf empty_wf hb

theorem mk_skip_left {α : Type u} {β : Type v} {b₁ b₂ : β} {s : β → β → Prop} (a₁ a₂ : α) (h : s b₁ b₂) :
    SkipLeft α s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ :=
  RevLex.right _ _ h

end

instance hasWellFounded {α : Type u} {β : α → Type v} [s₁ : HasWellFounded α] [s₂ : ∀ a, HasWellFounded (β a)] :
    HasWellFounded (PSigma β) where
  R := Lex s₁.R fun a => (s₂ a).R
  wf := lex_wf s₁.wf fun a => (s₂ a).wf

end PSigma

