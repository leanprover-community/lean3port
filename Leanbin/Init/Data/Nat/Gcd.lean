/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

Definitions and properties of gcd, lcm, and coprime.
-/
prelude
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Meta.WellFoundedTactics

open WellFounded

namespace Nat

attribute [simp] gcd_succ

theorem gcd_def (x y : ℕ) : gcd x y = if x = 0 then y else gcd (y % x) x := by
  cases x <;> simp

@[reducible]
def Coprime (m n : ℕ) : Prop :=
  m.coprime n

end Nat

