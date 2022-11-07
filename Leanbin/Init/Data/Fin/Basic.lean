/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Nat.Basic

open Nat

#print Fin /-
/-- `fin n` is the subtype of `ℕ` consisting of natural numbers strictly smaller than `n`. -/
structure Fin (n : ℕ) where
  val : Nat
  property : val < n
-/

attribute [pp_using_anonymous_constructor] Fin

namespace Fin

protected def Lt {n} (a b : Fin n) : Prop :=
  a.val < b.val

protected def Le {n} (a b : Fin n) : Prop :=
  a.val ≤ b.val

instance {n} : LT (Fin n) :=
  ⟨Fin.Lt⟩

instance {n} : LE (Fin n) :=
  ⟨Fin.Le⟩

instance decidableLt {n} (a b : Fin n) : Decidable (a < b) :=
  Nat.decidableLt _ _

instance decidableLe {n} (a b : Fin n) : Decidable (a ≤ b) :=
  Nat.decidableLe _ _

def elim0.{u} {α : Fin 0 → Sort u} : ∀ x : Fin 0, α x
  | ⟨n, h⟩ => absurd h n.not_lt_zero

variable {n : Nat}

#print Fin.eq_of_veq /-
theorem eq_of_veq : ∀ {i j : Fin n}, i.val = j.val → i = j
  | ⟨iv, ilt₁⟩, ⟨iv, ilt₂⟩, rfl => rfl
-/

#print Fin.veq_of_eq /-
theorem veq_of_eq : ∀ {i j : Fin n}, i = j → i.val = j.val
  | ⟨iv, ilt⟩, _, rfl => rfl
-/

#print Fin.ne_of_vne /-
theorem ne_of_vne {i j : Fin n} (h : i.val ≠ j.val) : i ≠ j := fun h' => absurd (veq_of_eq h') h
-/

#print Fin.vne_of_ne /-
theorem vne_of_ne {i j : Fin n} (h : i ≠ j) : i.val ≠ j.val := fun h' => absurd (eq_of_veq h') h
-/

end Fin

open Fin

instance (n : Nat) : DecidableEq (Fin n) := fun i j =>
  decidable_of_decidable_of_iff (Nat.decidableEq i.val j.val) ⟨eq_of_veq, veq_of_eq⟩

