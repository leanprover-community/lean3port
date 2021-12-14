prelude 
import Leanbin.Init.Data.Sigma.Basic 
import Leanbin.Init.Meta.Default

universe u v

namespace Psigma

section 

variable {α : Sort u} {β : α → Sort v}

variable (r : α → α → Prop)

variable (s : ∀ a, β a → β a → Prop)

inductive lex : Psigma β → Psigma β → Prop
  | left : ∀ {a₁ : α} b₁ : β a₁ {a₂ : α} b₂ : β a₂, r a₁ a₂ → lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  | right : ∀ a : α {b₁ b₂ : β a}, s a b₁ b₂ → lex ⟨a, b₁⟩ ⟨a, b₂⟩

end 

section 

open WellFounded Tactic

parameter {α : Sort u}{β : α → Sort v}

parameter {r : α → α → Prop}{s : ∀ a : α, β a → β a → Prop}

local infixl:50 "≺" => lex r s

theorem lex_accessible {a} (aca : Acc r a) (acb : ∀ a, WellFounded (s a)) : ∀ b : β a, Acc (lex r s) ⟨a, b⟩ :=
  Acc.recOnₓ aca
    fun xa aca iha : ∀ y, r y xa → ∀ b : β y, Acc (lex r s) ⟨y, b⟩ =>
      fun b : β xa =>
        Acc.recOnₓ (WellFounded.apply (acb xa) b)
          fun xb acb ihb : ∀ y : β xa, s xa y xb → Acc (lex r s) ⟨xa, y⟩ =>
            Acc.intro ⟨xa, xb⟩
              fun p lt : p≺⟨xa, xb⟩ =>
                have aux : xa = xa → HEq xb xb → Acc (lex r s) p :=
                  @Psigma.Lex.rec_on α β r s (fun p₁ p₂ => p₂.1 = xa → HEq p₂.2 xb → Acc (lex r s) p₁) p ⟨xa, xb⟩ lt
                    (fun a₁ : α b₁ : β a₁ a₂ : α b₂ : β a₂ h : r a₁ a₂ eq₂ : a₂ = xa eq₃ : HEq b₂ xb =>
                      by 
                        subst eq₂ 
                        exact iha a₁ h b₁)
                    fun a : α b₁ b₂ : β a h : s a b₁ b₂ eq₂ : a = xa eq₃ : HEq b₂ xb =>
                      by 
                        subst eq₂ 
                        have new_eq₃ := eq_of_heq eq₃ 
                        subst new_eq₃ 
                        exact ihb b₁ h 
                aux rfl (HEq.refl xb)

theorem lex_wf (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (lex r s) :=
  WellFounded.intro$ fun ⟨a, b⟩ => lex_accessible (WellFounded.apply ha a) hb b

end 

section 

parameter {α : Sort u}{β : Sort v}

def lex_ndep (r : α → α → Prop) (s : β → β → Prop) :=
  lex r fun a : α => s

theorem lex_ndep_wf {r : α → α → Prop} {s : β → β → Prop} (ha : WellFounded r) (hb : WellFounded s) :
  WellFounded (lex_ndep r s) :=
  WellFounded.intro$ fun ⟨a, b⟩ => lex_accessible (WellFounded.apply ha a) (fun x => hb) b

end 

section 

variable {α : Sort u} {β : Sort v}

variable (r : α → α → Prop)

variable (s : β → β → Prop)

inductive rev_lex : (@Psigma α fun a => β) → (@Psigma α fun a => β) → Prop
  | left : ∀ {a₁ a₂ : α} b : β, r a₁ a₂ → rev_lex ⟨a₁, b⟩ ⟨a₂, b⟩
  | right : ∀ a₁ : α {b₁ : β} a₂ : α {b₂ : β}, s b₁ b₂ → rev_lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩

end 

section 

open WellFounded Tactic

parameter {α : Sort u}{β : Sort v}

parameter {r : α → α → Prop}{s : β → β → Prop}

local infixl:50 "≺" => rev_lex r s

theorem rev_lex_accessible {b} (acb : Acc s b) (aca : ∀ a, Acc r a) : ∀ a, Acc (rev_lex r s) ⟨a, b⟩ :=
  Acc.recOnₓ acb
    fun xb acb ihb : ∀ y, s y xb → ∀ a, Acc (rev_lex r s) ⟨a, y⟩ =>
      fun a =>
        Acc.recOnₓ (aca a)
          fun xa aca iha : ∀ y, r y xa → Acc (rev_lex r s) (mk y xb) =>
            Acc.intro ⟨xa, xb⟩
              fun p lt : p≺⟨xa, xb⟩ =>
                have aux : xa = xa → xb = xb → Acc (rev_lex r s) p :=
                  @rev_lex.rec_on α β r s (fun p₁ p₂ => fst p₂ = xa → snd p₂ = xb → Acc (rev_lex r s) p₁) p ⟨xa, xb⟩ lt
                    (fun a₁ a₂ b h : r a₁ a₂ eq₂ : a₂ = xa eq₃ : b = xb =>
                      show Acc (rev_lex r s) ⟨a₁, b⟩ from
                        have r₁ : r a₁ xa := Eq.recOnₓ eq₂ h 
                        have aux : Acc (rev_lex r s) ⟨a₁, xb⟩ := iha a₁ r₁ 
                        Eq.recOnₓ (Eq.symm eq₃) aux)
                    fun a₁ b₁ a₂ b₂ h : s b₁ b₂ eq₂ : a₂ = xa eq₃ : b₂ = xb =>
                      show Acc (rev_lex r s) (mk a₁ b₁) from
                        have s₁ : s b₁ xb := Eq.recOnₓ eq₃ h 
                        ihb b₁ s₁ a₁ 
                aux rfl rfl

theorem rev_lex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (rev_lex r s) :=
  WellFounded.intro$ fun ⟨a, b⟩ => rev_lex_accessible (apply hb b) (WellFounded.apply ha) a

end 

section 

def skip_left (α : Type u) {β : Type v} (s : β → β → Prop) : (@Psigma α fun a => β) → (@Psigma α fun a => β) → Prop :=
  rev_lex EmptyRelation s

theorem skip_left_wf (α : Type u) {β : Type v} {s : β → β → Prop} (hb : WellFounded s) : WellFounded (skip_left α s) :=
  rev_lex_wf empty_wf hb

theorem mk_skip_left {α : Type u} {β : Type v} {b₁ b₂ : β} {s : β → β → Prop} (a₁ a₂ : α) (h : s b₁ b₂) :
  skip_left α s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ :=
  rev_lex.right _ _ h

end 

instance HasWellFounded {α : Type u} {β : α → Type v} [s₁ : HasWellFounded α] [s₂ : ∀ a, HasWellFounded (β a)] :
  HasWellFounded (Psigma β) :=
  { R := lex s₁.r fun a => (s₂ a).R, wf := lex_wf s₁.wf fun a => (s₂ a).wf }

end Psigma

