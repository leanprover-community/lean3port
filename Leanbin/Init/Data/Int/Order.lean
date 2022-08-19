/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers.
-/
prelude
import Leanbin.Init.Data.Int.Basic
import Leanbin.Init.Data.Ordering.Basic

namespace Int

open private decNonneg from Init.Data.Int.Basic in
def decidableNonNeg (a : ℤ) : Decidable (NonNeg a) :=
  decNonneg _

@[simp]
theorem zero_le_cast (n : Nat) : 0 ≤ (n : Int) := by
  norm_cast; simp

theorem Le.intro_sub {a b : ℤ} {n : ℕ} (h : b - a = n) : a ≤ b :=
  Int.le_of_sub_nonneg (by simp [h])

attribute [local simp]
  Int.sub_eq_add_neg Int.add_assoc Int.add_right_neg Int.add_left_neg Int.zero_add Int.add_zero Int.neg_add Int.neg_neg Int.neg_zero

theorem Le.intro {a b : ℤ} {n : ℕ} (h : a + n = b) : a ≤ b :=
  Le.intro_sub (n := n)
    (by rw [← h, Int.add_comm] <;> simp)

theorem Le.dest_sub {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, b - a = n :=
  NonNeg.elim h

theorem Le.dest {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, a + n = b :=
  match Le.dest_sub h with
  | ⟨n, h₁⟩ =>
    Exists.intro n
      (by
        rw [← h₁, Int.add_comm]
        simp )

theorem Le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
  Exists.elim (Le.dest h) h'

theorem coe_nat_le_coe_nat_of_le {m n : ℕ} (h : m ≤ n) : (↑m : ℤ) ≤ ↑n :=
  match Nat.Le.dest h with
  | ⟨k, (hk : m + k = n)⟩ =>
    Le.intro (n := k) (by rw [← hk]; rfl)

theorem le_of_coe_nat_le_coe_nat {m n : ℕ} (h : (↑m : ℤ) ≤ ↑n) : m ≤ n :=
  Le.elim h fun k h => by
    norm_cast at h
    rw [← h]
    exact Nat.le_add_right m k

theorem coe_nat_le_coe_nat_iff (m n : ℕ) : (↑m : ℤ) ≤ ↑n ↔ m ≤ n :=
  Iff.intro le_of_coe_nat_le_coe_nat coe_nat_le_coe_nat_of_le

theorem coe_zero_le (n : ℕ) : 0 ≤ (↑n : ℤ) :=
  coe_nat_le_coe_nat_of_le n.zero_le

theorem eq_coe_of_zero_le {a : ℤ} (h : 0 ≤ a) : ∃ n : ℕ, a = n := by
  have t := le.dest_sub h
  simp at t
  exact t

theorem Lt.intro {a b : ℤ} {n : ℕ} (h : a + Nat.succ n = b) : a < b :=
  h ▸ lt_add_succ a n

theorem Lt.dest {a b : ℤ} (h : a < b) : ∃ n : ℕ, a + ↑(Nat.succ n) = b :=
  Le.elim h fun n => fun hn : a + 1 + n = b =>
    Exists.intro n
      (by
        rw [← hn, Int.add_assoc, Int.add_comm 1]
        rfl)

theorem Lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(Nat.succ n) = b → P) : P :=
  Exists.elim (Lt.dest h) h'

theorem coe_nat_lt_coe_nat_iff (n m : ℕ) : (↑n : ℤ) < ↑m ↔ n < m := by
  rw [lt_iff_add_one_le, ← Int.coe_nat_succ, coe_nat_le_coe_nat_iff]
  rfl

theorem lt_of_coe_nat_lt_coe_nat {m n : ℕ} (h : (↑m : ℤ) < ↑n) : m < n :=
  (coe_nat_lt_coe_nat_iff _ _).mp h

theorem coe_nat_lt_coe_nat_of_lt {m n : ℕ} (h : m < n) : (↑m : ℤ) < ↑n :=
  (coe_nat_lt_coe_nat_iff _ _).mpr h

theorem eq_nat_abs_of_zero_le {a : ℤ} (h : 0 ≤ a) : a = natAbs a := by
  let ⟨n, e⟩ := eq_coe_of_zero_le h
  rw [e] <;> rfl

theorem le_nat_abs {a : ℤ} : a ≤ natAbs a :=
  Or.elim (le_total 0 a)
    (fun h => by simp [← eq_nat_abs_of_zero_le h])
    fun h => le_trans h (coe_zero_le _)

attribute [local simp] neg_mul_eq_neg_mul_symm mul_neg_eq_neg_mul_symm

-- more facts specific to int
theorem of_nat_nonneg (n : ℕ) : 0 ≤ ofNat n :=
  ofNat_nonneg n

theorem coe_succ_pos (n : Nat) : 0 < (Nat.succ n : ℤ) :=
  coe_nat_lt_coe_nat_of_lt (Nat.succ_pos _)

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : ∃ n : ℕ, a = -(n : ℤ) :=
  let ⟨n, h⟩ := eq_coe_of_zero_le (Int.neg_nonneg_of_nonpos H)
  ⟨n, Int.eq_neg_of_eq_neg h.symm⟩

theorem nat_abs_of_nonneg {a : ℤ} (H : 0 ≤ a) : (natAbs a : ℤ) = a :=
  match a, eq_coe_of_zero_le H with
  | _, ⟨n, rfl⟩ => rfl

theorem of_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : (natAbs a : ℤ) = -a := by
  rw [← nat_abs_neg, nat_abs_of_nonneg (Int.neg_nonneg_of_nonpos H)]

end Int

