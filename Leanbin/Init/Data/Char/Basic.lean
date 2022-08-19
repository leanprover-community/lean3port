/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Nat.Basic

open Nat

@[reducible]
def IsValidChar (n : Nat) : Prop :=
  Nat.isValidChar n

theorem is_valid_char_range_1 (n : Nat) (h : n < 55296) : IsValidChar n :=
  Or.inl h

theorem is_valid_char_range_2 (n : Nat) (h₁ : 57343 < n) (h₂ : n < 1114112) : IsValidChar n :=
  Or.inr ⟨h₁, h₂⟩

namespace Char

protected def Lt (a b : Char) : Prop :=
  a.val < b.val

protected def Le (a b : Char) : Prop :=
  a.val ≤ b.val

/-
We cannot use tactics dec_trivial or comp_val here because the tactic framework has not been defined yet.
We also do not use `zero_lt_succ _` as a proof term because this proof may not be trivial to check by
external type checkers. See discussion at: https://github.com/leanprover/tc/issues/8
-/
theorem zero_lt_d800 : 0 < 55296 :=
  Nat.zero_lt_bit0 <|
    Nat.bit0_ne_zero <|
      Nat.bit0_ne_zero <|
        Nat.bit0_ne_zero <|
          Nat.bit0_ne_zero <|
            Nat.bit0_ne_zero <|
              Nat.bit0_ne_zero <|
                Nat.bit0_ne_zero <| Nat.bit0_ne_zero <| Nat.bit0_ne_zero <| Nat.bit0_ne_zero <| Nat.bit1_ne_zero 13

theorem eq_of_veq : ∀ {c d : Char}, c.toNat = d.toNat → c = d
  | ⟨⟨_, _⟩, _⟩, _, rfl => rfl

theorem veq_of_eq : ∀ {c d : Char}, c = d → c.toNat = d.toNat
  | _, _, rfl => rfl

theorem ne_of_vne {c d : Char} (h : c.toNat ≠ d.toNat) : c ≠ d := fun h' => absurd (veq_of_eq h') h

theorem vne_of_ne {c d : Char} (h : c ≠ d) : c.toNat ≠ d.toNat := fun h' => absurd (eq_of_veq h') h

end Char

