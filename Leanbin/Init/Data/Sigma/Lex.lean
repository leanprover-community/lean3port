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

open WellFounded Tactic

variable {α : Sort u}{β : α → Sort v}

variable {r : α → α → Prop}{s : ∀ a : α, β a → β a → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => Lex r s

theorem lex_accessible {a} (aca : Acc r a) (acb : ∀ a, WellFounded (s a)) : ∀ b : β a, Acc (Lex r s) ⟨a, b⟩ :=
  lexAccessible aca acb

-- The lexicographical order of well founded relations is well-founded
theorem lex_wf (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lex_accessible (WellFounded.apply ha a) hb b

end

section

variable {α : Sort u}{β : Sort v}

def LexNdep (r : α → α → Prop) (s : β → β → Prop) :=
  Lex r fun a : α => s

theorem lex_ndep_wf {r : α → α → Prop} {s : β → β → Prop} (ha : WellFounded r) (hb : WellFounded s) :
    WellFounded (LexNdep r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lex_accessible (WellFounded.apply ha a) (fun x => hb) b

end

section

open WellFounded Tactic

variable {α : Sort u}{β : Sort v}

variable {r : α → α → Prop}{s : β → β → Prop}

theorem rev_lex_accessible {b} (acb : Acc s b) (aca : ∀ a, Acc r a) : ∀ a, Acc (RevLex r s) ⟨a, b⟩ :=
  revLexAccessible acb aca

theorem rev_lex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => rev_lex_accessible (apply hb b) (WellFounded.apply ha) a

end

section

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

