/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic

namespace Nat

instance : Inhabited ℕ :=
  ⟨Nat.zero⟩

@[simp]
theorem nat_zero_eq_zero : Nat.zero = 0 :=
  rfl

-- Basic lemmas for comparing numerals
protected theorem bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
  show succ (succ n + n) = succ (succ (n + n)) from congr_arg succ (succ_add n n)

protected theorem zero_lt_bit0 : ∀ {n : Nat}, n ≠ 0 → 0 < bit0 n
  | 0, h => absurd rfl h
  | succ n, h =>
    calc
      0 < succ (succ (bit0 n)) := zero_lt_succ _
      _ = bit0 (succ n) := (Nat.bit0_succ_eq n).symm

protected theorem zero_lt_bit1 (n : Nat) : 0 < bit1 n :=
  zero_lt_succ _

protected theorem bit0_ne_zero : ∀ {n : ℕ}, n ≠ 0 → bit0 n ≠ 0
  | 0, h => absurd rfl h
  | n + 1, h =>
    suffices n + 1 + (n + 1) ≠ 0 from this
    suffices succ (n + 1 + n) ≠ 0 from this
    fun h => Nat.noConfusion h

protected theorem bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
  show succ (n + n) ≠ 0 from fun h => Nat.noConfusion h

end Nat

