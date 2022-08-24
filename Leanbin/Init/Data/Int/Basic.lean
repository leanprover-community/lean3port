/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
prelude
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Data.Nat.Gcd

open Nat

namespace Int

protected theorem coe_nat_eq (n : ℕ) : ↑n = Int.ofNat n :=
  rfl

protected abbrev zero : ℤ :=
  0

protected abbrev one : ℤ :=
  1

theorem of_nat_zero : ofNat (0 : Nat) = (0 : Int) :=
  rfl

theorem of_nat_one : ofNat (1 : Nat) = (1 : Int) :=
  rfl

-- m < n, and n - m = succ k
theorem sub_nat_nat_of_sub_eq_zero {m n : ℕ} (h : n - m = 0) : subNatNat m n = ofNat (m - n) :=
  subNatNat_of_sub_eq_zero h

theorem sub_nat_nat_of_sub_eq_succ {m n k : ℕ} (h : n - m = succ k) : subNatNat m n = -[1+ k] :=
  subNatNat_of_sub_eq_succ h

theorem of_nat_add (n m : ℕ) : ofNat (n + m) = ofNat n + ofNat m :=
  rfl

theorem of_nat_mul (n m : ℕ) : ofNat (n * m) = ofNat n * ofNat m :=
  rfl

theorem of_nat_succ (n : ℕ) : ofNat (succ n) = ofNat n + 1 :=
  rfl

theorem neg_of_nat_zero : -ofNat 0 = 0 :=
  rfl

theorem neg_of_nat_of_succ (n : ℕ) : -ofNat (succ n) = -[1+ n] :=
  rfl

theorem neg_neg_of_nat_succ (n : ℕ) : - -[1+ n] = ofNat (succ n) :=
  rfl

theorem of_nat_eq_coe (n : ℕ) : ofNat n = ↑n :=
  rfl

theorem neg_succ_of_nat_coe (n : ℕ) : -[1+ n] = -↑(n + 1) :=
  rfl

protected theorem coe_nat_add (m n : ℕ) : (↑(m + n) : ℤ) = ↑m + ↑n :=
  rfl

protected theorem coe_nat_mul (m n : ℕ) : (↑(m * n) : ℤ) = ↑m * ↑n :=
  rfl

protected theorem coe_nat_zero : ↑(0 : ℕ) = (0 : ℤ) :=
  rfl

protected theorem coe_nat_one : ↑(1 : ℕ) = (1 : ℤ) :=
  rfl

protected theorem coe_nat_succ (n : ℕ) : (↑(succ n) : ℤ) = ↑n + 1 :=
  rfl

protected theorem coe_nat_add_out (m n : ℕ) : ↑m + ↑n = (m + n : ℤ) :=
  rfl

protected theorem coe_nat_mul_out (m n : ℕ) : ↑m * ↑n = (↑(m * n) : ℤ) :=
  rfl

protected theorem coe_nat_add_one_out (n : ℕ) : ↑n + (1 : ℤ) = ↑(succ n) :=
  rfl

-- these are only for internal use
theorem of_nat_add_of_nat (m n : Nat) : ofNat m + ofNat n = ofNat (m + n) :=
  rfl

theorem of_nat_add_neg_succ_of_nat (m n : Nat) : ofNat m + -[1+ n] = subNatNat m (succ n) :=
  rfl

theorem neg_succ_of_nat_add_of_nat (m n : Nat) : -[1+ m] + ofNat n = subNatNat n (succ m) :=
  rfl

theorem neg_succ_of_nat_add_neg_succ_of_nat (m n : Nat) : -[1+ m] + -[1+ n] = -[1+ succ (m + n)] :=
  rfl

theorem of_nat_mul_of_nat (m n : Nat) : ofNat m * ofNat n = ofNat (m * n) :=
  rfl

theorem of_nat_mul_neg_succ_of_nat (m n : Nat) : ofNat m * -[1+ n] = negOfNat (m * succ n) :=
  rfl

theorem neg_succ_of_nat_of_nat (m n : Nat) : -[1+ m] * ofNat n = negOfNat (succ m * n) :=
  rfl

theorem mul_neg_succ_of_nat_neg_succ_of_nat (m n : Nat) : -[1+ m] * -[1+ n] = ofNat (succ m * succ n) :=
  rfl

attribute [local simp]
  of_nat_add_of_nat of_nat_mul_of_nat neg_of_nat_zero neg_of_nat_of_succ neg_neg_of_nat_succ of_nat_add_neg_succ_of_nat neg_succ_of_nat_add_of_nat neg_succ_of_nat_add_neg_succ_of_nat of_nat_mul_neg_succ_of_nat neg_succ_of_nat_of_nat mul_neg_succ_of_nat_neg_succ_of_nat

theorem of_nat_eq_of_nat_iff (m n : ℕ) : ofNat m = ofNat n ↔ m = n :=
  Iff.intro Int.ofNat.inj (congr_arg _)

protected theorem coe_nat_eq_coe_nat_iff (m n : ℕ) : (↑m : ℤ) = ↑n ↔ m = n :=
  of_nat_eq_of_nat_iff m n

theorem neg_succ_of_nat_inj_iff {m n : ℕ} : negSucc m = negSucc n ↔ m = n :=
  ⟨negSucc.inj, fun H => by
    simp [H]⟩

theorem neg_succ_of_nat_eq (n : ℕ) : -[1+ n] = -(n + 1 : ℤ) :=
  rfl

-- basic properties of sub_nat_nat
theorem sub_nat_nat_elim (m n : ℕ) (P : ℕ → ℕ → ℤ → Prop) (hp : ∀ i n, P (n + i) n (ofNat i))
    (hn : ∀ i m, P m (m + i + 1) -[1+ i]) : P m n (subNatNat m n) :=
  subNatNat_elim m n P hp hn

theorem sub_nat_nat_add_left {m n : ℕ} : subNatNat (m + n) m = ofNat n :=
  subNatNat_add_left

theorem sub_nat_nat_add_right {m n : ℕ} : subNatNat m (m + n + 1) = negSucc n :=
  subNatNat_add_right

theorem sub_nat_nat_add_add (m n k : ℕ) : subNatNat (m + k) (n + k) = subNatNat m n :=
  subNatNat_add_add ..

theorem sub_nat_nat_of_le {m n : ℕ} (h : n ≤ m) : subNatNat m n = ofNat (m - n) :=
  sub_nat_nat_of_sub_eq_zero (Nat.sub_eq_zero_of_le h)

theorem sub_nat_nat_of_lt {m n : ℕ} (h : m < n) : subNatNat m n = -[1+ pred (n - m)] := by
  have : n - m = succ (pred (n - m)) := Eq.symm (succ_pred_eq_of_pos (Nat.sub_pos_of_lt h))
  rw [sub_nat_nat_of_sub_eq_succ this]

theorem nat_abs_of_nat (n : ℕ) : natAbs ↑n = n :=
  rfl

theorem eq_zero_of_nat_abs_eq_zero : ∀ {a : ℤ}, natAbs a = 0 → a = 0
  | ofNat m, H => congr_arg ofNat H
  | -[1+ m'], H => absurd H (succ_ne_zero _)

theorem nat_abs_pos_of_ne_zero {a : ℤ} (h : a ≠ 0) : 0 < natAbs a :=
  (Nat.eq_zero_or_pos _).resolve_left <| mt eq_zero_of_nat_abs_eq_zero h

theorem nat_abs_zero : natAbs (0 : Int) = (0 : Nat) :=
  rfl

theorem nat_abs_one : natAbs (1 : Int) = (1 : Nat) :=
  rfl

theorem nat_abs_mul_self : ∀ {a : ℤ}, ↑(natAbs a * natAbs a) = a * a
  | ofNat m => rfl
  | -[1+ m'] => rfl

@[simp]
theorem nat_abs_neg (a : ℤ) : natAbs (-a) = natAbs a := by
  cases' a with n n
  cases n <;> rfl
  rfl

theorem nat_abs_eq : ∀ a : ℤ, a = natAbs a ∨ a = -(natAbs a : ℤ)
  | ofNat m => Or.inl rfl
  | -[1+ m'] => Or.inr rfl

theorem eq_coe_or_neg (a : ℤ) : ∃ n : ℕ, a = n ∨ a = -(n : ℤ) :=
  ⟨_, nat_abs_eq a⟩

theorem sub_nat_nat_sub {m n : ℕ} (h : n ≤ m) (k : ℕ) : subNatNat (m - n) k = subNatNat m (k + n) :=
  subNatNat_sub h k

theorem sub_nat_nat_add (m n k : ℕ) : subNatNat (m + n) k = ofNat m + subNatNat n k :=
  subNatNat_add m n k

theorem sub_nat_nat_add_neg_succ_of_nat (m n k : ℕ) : subNatNat m n + -[1+ k] = subNatNat m (n + succ k) :=
  subNatNat_add_negSucc_ofNat m n k

theorem of_nat_mul_neg_of_nat (m : ℕ) : ∀ n, ofNat m * negOfNat n = negOfNat (m * n) :=
  ofNat_mul_negOfNat m

theorem neg_of_nat_mul_of_nat (m n : ℕ) : negOfNat m * ofNat n = negOfNat (m * n) :=
  negOfNat_mul_ofNat m n

theorem neg_succ_of_nat_mul_neg_of_nat (m : ℕ) : ∀ n, -[1+ m] * negOfNat n = ofNat (succ m * n) :=
  negSucc_ofNat_mul_negOfNat m

theorem neg_of_nat_mul_neg_succ_of_nat (m n : ℕ) : negOfNat n * -[1+ m] = ofNat (n * succ m) :=
  negOfNat_mul_negSucc_ofNat m n

theorem neg_of_nat_eq_sub_nat_nat_zero : ∀ n, negOfNat n = subNatNat 0 n
  | 0 => rfl
  | succ n => rfl

theorem of_nat_mul_sub_nat_nat (m n k : ℕ) : ofNat m * subNatNat n k = subNatNat (m * n) (m * k) :=
  ofNat_mul_subNatNat m n k

theorem neg_of_nat_add (m n : ℕ) : negOfNat m + negOfNat n = negOfNat (m + n) :=
  negOfNat_add m n

theorem neg_succ_of_nat_mul_sub_nat_nat (m n k : ℕ) : -[1+ m] * subNatNat n k = subNatNat (succ m * k) (succ m * n) :=
  negSucc_ofNat_mul_subNatNat ..

theorem of_nat_sub {n m : ℕ} (h : m ≤ n) : ofNat (n - m) = ofNat n - ofNat m :=
  ofNat_sub h

theorem neg_succ_of_nat_coe' (n : ℕ) : -[1+ n] = -↑n - 1 := by
  rw [Int.sub_eq_add_neg, ← Int.neg_add] <;> rfl

protected theorem sub_nat_nat_eq_coe {m n : ℕ} : subNatNat m n = ↑m - ↑n :=
  Int.subNatNat_eq_coe

theorem to_nat_sub (m n : ℕ) : toNat (m - n : Nat) = m - n :=
  toNat_sub m n

theorem sign_mul_nat_abs : ∀ a : ℤ, sign a * natAbs a = a
  | (n + 1 : ℕ) => Int.one_mul _
  | 0 => rfl
  | -[1+ n] => (Int.neg_eq_neg_one_mul _).symm

end Int

