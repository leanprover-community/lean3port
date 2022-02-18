prelude
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Meta.WellFoundedTactics

open WellFounded

namespace Nat

def gcd : Nat → Nat → Nat
  | 0, y => y
  | succ x, y =>
    have : y % succ x < succ x := mod_ltₓ _ <| succ_posₓ _
    gcd (y % succ x) (succ x)

@[simp]
theorem gcd_zero_left (x : Nat) : gcdₓ 0 x = x := by
  simp [gcd]

@[simp]
theorem gcd_succ (x y : Nat) : gcdₓ (succ x) y = gcdₓ (y % succ x) (succ x) := by
  simp [gcd]

@[simp]
theorem gcd_one_left (n : ℕ) : gcdₓ 1 n = 1 := by
  simp [gcd]

theorem gcd_def (x y : ℕ) : gcdₓ x y = if x = 0 then y else gcdₓ (y % x) x := by
  cases x <;> simp [gcd, succ_ne_zero]

@[simp]
theorem gcd_self (n : ℕ) : gcdₓ n n = n := by
  cases n <;> simp [gcd, mod_self]

@[simp]
theorem gcd_zero_right (n : ℕ) : gcdₓ n 0 = n := by
  cases n <;> simp [gcd]

theorem gcd_rec (m n : ℕ) : gcdₓ m n = gcdₓ (n % m) m := by
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
  m * n / gcdₓ m n

@[reducible]
def coprime (m n : ℕ) : Prop :=
  gcdₓ m n = 1

end Nat

