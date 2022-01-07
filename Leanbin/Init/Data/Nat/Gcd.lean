prelude
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Meta.WellFoundedTactics

open WellFounded

namespace Nat

def gcd : Nat → Nat → Nat
  | 0, y => y
  | succ x, y =>
    have : y % succ x < succ x := mod_lt _ $ succ_pos _
    gcd (y % succ x) (succ x)

@[simp]
theorem gcd_zero_left (x : Nat) : gcd 0 x = x := by
  simp [gcd]

@[simp]
theorem gcd_succ (x y : Nat) : gcd (succ x) y = gcd (y % succ x) (succ x) := by
  simp [gcd]

@[simp]
theorem gcd_one_left (n : ℕ) : gcd 1 n = 1 := by
  simp [gcd]

theorem gcd_def (x y : ℕ) : gcd x y = if x = 0 then y else gcd (y % x) x := by
  cases x <;> simp [gcd, succ_ne_zero]

@[simp]
theorem gcd_self (n : ℕ) : gcd n n = n := by
  cases n <;> simp [gcd, mod_self]

@[simp]
theorem gcd_zero_right (n : ℕ) : gcd n 0 = n := by
  cases n <;> simp [gcd]

theorem gcd_rec (m n : ℕ) : gcd m n = gcd (n % m) m := by
  cases m <;> simp [gcd]

@[elab_as_eliminator]
theorem gcd.induction {P : ℕ → ℕ → Prop} (m n : ℕ) (H0 : ∀ n, P 0 n) (H1 : ∀ m n, 0 < m → P (n % m) m → P m n) :
    P m n :=
  @induction _ _ lt_wf (fun m => ∀ n, P m n) m
    (fun k IH => by
      induction' k with k ih
      exact H0
      exact fun n => H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _))
    n

def lcm (m n : ℕ) : ℕ :=
  m * n / gcd m n

@[reducible]
def coprime (m n : ℕ) : Prop :=
  gcd m n = 1

end Nat

