prelude
import Leanbin.Init.Logic
import Leanbin.Init.Wf

notation3 "Σ " (...) ", " r:(scoped p => Sigma p) => r

notation3 "Σ' " (...) ", " r:(scoped p => Psigma p) => r

universe u v

theorem ex_of_psig {α : Type u} {p : α → Prop} : (Σ' x, p x) → ∃ x, p x
  | ⟨x, hx⟩ => ⟨x, hx⟩

section

variable {α : Type u} {β : α → Type v}

protected theorem Sigma.eq : ∀ {p₁ p₂ : Σ a : α, β a} h₁ : p₁.1 = p₂.1, (Eq.recOnₓ h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨a, b⟩, ⟨a, b⟩, rfl, rfl => rfl

end

section

variable {α : Sort u} {β : α → Sort v}

protected theorem Psigma.eq : ∀ {p₁ p₂ : Psigma β} h₁ : p₁.1 = p₂.1, (Eq.recOnₓ h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨a, b⟩, ⟨a, b⟩, rfl, rfl => rfl

end

