prelude
import Leanbin.Init.Data.Nat.Basic

open Nat

@[reducible]
def IsValidChar (n : Nat) : Prop :=
  n < 55296 ∨ 57343 < n ∧ n < 1114112

theorem is_valid_char_range_1 (n : Nat) (h : n < 55296) : IsValidChar n :=
  Or.inl h

theorem is_valid_char_range_2 (n : Nat) (h₁ : 57343 < n) (h₂ : n < 1114112) : IsValidChar n :=
  Or.inr ⟨h₁, h₂⟩

/-- The `char` type represents an unicode scalar value.
    See http://www.unicode.org/glossary/#unicode_scalar_value). -/
structure Charₓ where
  val : Nat
  valid : IsValidChar val

instance : SizeOf Charₓ :=
  ⟨fun c => c.val⟩

namespace Charₓ

protected def lt (a b : Charₓ) : Prop :=
  a.val < b.val

protected def le (a b : Charₓ) : Prop :=
  a.val ≤ b.val

instance : LT Charₓ :=
  ⟨Charₓ.Lt⟩

instance : LE Charₓ :=
  ⟨Charₓ.Le⟩

instance decidable_lt (a b : Charₓ) : Decidable (a < b) :=
  Nat.decidableLt _ _

instance decidable_le (a b : Charₓ) : Decidable (a ≤ b) :=
  Nat.decidableLe _ _

theorem zero_lt_d800 : 0 < 55296 :=
  Nat.zero_lt_bit0 $
    Nat.bit0_ne_zero $
      Nat.bit0_ne_zero $
        Nat.bit0_ne_zero $
          Nat.bit0_ne_zero $
            Nat.bit0_ne_zero $
              Nat.bit0_ne_zero $
                Nat.bit0_ne_zero $ Nat.bit0_ne_zero $ Nat.bit0_ne_zero $ Nat.bit0_ne_zero $ Nat.bit1_ne_zero 13

@[matchPattern]
def of_nat (n : Nat) : Charₓ :=
  if h : IsValidChar n then { val := n, valid := h } else { val := 0, valid := Or.inl zero_lt_d800 }

def to_nat (c : Charₓ) : Nat :=
  c.val

theorem eq_of_veq : ∀ {c d : Charₓ}, c.val = d.val → c = d
  | ⟨v, h⟩, ⟨_, _⟩, rfl => rfl

theorem veq_of_eq : ∀ {c d : Charₓ}, c = d → c.val = d.val
  | _, _, rfl => rfl

theorem ne_of_vne {c d : Charₓ} (h : c.val ≠ d.val) : c ≠ d := fun h' => absurd (veq_of_eq h') h

theorem vne_of_ne {c d : Charₓ} (h : c ≠ d) : c.val ≠ d.val := fun h' => absurd (eq_of_veq h') h

end Charₓ

instance : DecidableEq Charₓ := fun i j =>
  decidableOfDecidableOfIff (Nat.decidableEq i.val j.val) ⟨Charₓ.eq_of_veq, Charₓ.veq_of_eq⟩

instance : Inhabited Charₓ :=
  ⟨'A'⟩

