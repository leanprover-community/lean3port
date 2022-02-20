/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Nat.Basic

open Nat

/-- `fin n` is the subtype of `ℕ` consisting of natural numbers strictly smaller than `n`. -/
def Finₓ (n : ℕ) :=
  { i : ℕ // i < n }

namespace Finₓ

/-- Backwards-compatible constructor for `fin n`. -/
def mk {n : ℕ} i h : Finₓ n :=
  ⟨i, h⟩

protected def Lt {n} (a b : Finₓ n) : Prop :=
  a.val < b.val

protected def Le {n} (a b : Finₓ n) : Prop :=
  a.val ≤ b.val

instance {n} : LT (Finₓ n) :=
  ⟨Finₓ.Lt⟩

instance {n} : LE (Finₓ n) :=
  ⟨Finₓ.Le⟩

instance decidableLt {n} (a b : Finₓ n) : Decidable (a < b) :=
  Nat.decidableLt _ _

instance decidableLe {n} (a b : Finₓ n) : Decidable (a ≤ b) :=
  Nat.decidableLe _ _

def elim0.{u} {α : Finₓ 0 → Sort u} : ∀ x : Finₓ 0, α x
  | ⟨n, h⟩ => absurd h n.not_lt_zero

variable {n : Nat}

theorem eq_of_veq : ∀ {i j : Finₓ n}, i.val = j.val → i = j
  | ⟨iv, ilt₁⟩, ⟨iv, ilt₂⟩, rfl => rfl

theorem veq_of_eq : ∀ {i j : Finₓ n}, i = j → i.val = j.val
  | ⟨iv, ilt⟩, _, rfl => rfl

theorem ne_of_vne {i j : Finₓ n} (h : i.val ≠ j.val) : i ≠ j := fun h' => absurd (veq_of_eq h') h

theorem vne_of_ne {i j : Finₓ n} (h : i ≠ j) : i.val ≠ j.val := fun h' => absurd (eq_of_veq h') h

end Finₓ

open Finₓ

instance (n : Nat) : DecidableEq (Finₓ n) := fun i j =>
  decidableOfDecidableOfIff (Nat.decidableEq i.val j.val) ⟨eq_of_veq, veq_of_eq⟩

