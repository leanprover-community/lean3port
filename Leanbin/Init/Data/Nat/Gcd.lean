/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

-/
prelude
import Init.Data.Nat.Lemmas
import Init.Meta.WellFoundedTactics

#align_import init.data.nat.gcd from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

/-!
# Definitions and properties of gcd, lcm, and coprime
-/


open WellFounded

namespace Nat

/-! gcd -/


#print Nat.gcd /-
def gcd : Nat → Nat → Nat
  | 0, y => y
  | succ x, y =>
    have : y % succ x < succ x := mod_lt _ <| succ_pos _
    gcd (y % succ x) (succ x)
#align nat.gcd Nat.gcd
-/

#print Nat.gcd_zero_left /-
@[simp]
theorem gcd_zero_left (x : Nat) : gcd 0 x = x := by simp [gcd]
#align nat.gcd_zero_left Nat.gcd_zero_left
-/

#print Nat.gcd_succ /-
@[simp]
theorem gcd_succ (x y : Nat) : gcd (succ x) y = gcd (y % succ x) (succ x) := by simp [gcd]
#align nat.gcd_succ Nat.gcd_succ
-/

#print Nat.gcd_one_left /-
@[simp]
theorem gcd_one_left (n : ℕ) : gcd 1 n = 1 := by simp [gcd]
#align nat.gcd_one_left Nat.gcd_one_left
-/

#print Nat.gcd_def /-
theorem gcd_def (x y : ℕ) : gcd x y = if x = 0 then y else gcd (y % x) x := by
  cases x <;> simp [gcd, succ_ne_zero]
#align nat.gcd_def Nat.gcd_def
-/

#print Nat.gcd_self /-
@[simp]
theorem gcd_self (n : ℕ) : gcd n n = n := by cases n <;> simp [gcd, mod_self]
#align nat.gcd_self Nat.gcd_self
-/

#print Nat.gcd_zero_right /-
@[simp]
theorem gcd_zero_right (n : ℕ) : gcd n 0 = n := by cases n <;> simp [gcd]
#align nat.gcd_zero_right Nat.gcd_zero_right
-/

#print Nat.gcd_rec /-
theorem gcd_rec (m n : ℕ) : gcd m n = gcd (n % m) m := by cases m <;> simp [gcd]
#align nat.gcd_rec Nat.gcd_rec
-/

#print Nat.gcd.induction /-
@[elab_as_elim]
theorem gcd.induction {P : ℕ → ℕ → Prop} (m n : ℕ) (H0 : ∀ n, P 0 n)
    (H1 : ∀ m n, 0 < m → P (n % m) m → P m n) : P m n :=
  @induction _ _ lt_wfRel (fun m => ∀ n, P m n) m
    (fun k IH => by
      induction' k with k ih; exact H0
      exact fun n => H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _))
    n
#align nat.gcd.induction Nat.gcd.induction
-/

#print Nat.lcm /-
def lcm (m n : ℕ) : ℕ :=
  m * n / gcd m n
#align nat.lcm Nat.lcm
-/

#print Nat.Coprime /-
@[reducible]
def Coprime (m n : ℕ) : Prop :=
  gcd m n = 1
#align nat.coprime Nat.Coprime
-/

end Nat

