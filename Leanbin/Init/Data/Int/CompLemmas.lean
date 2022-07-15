/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Auxiliary lemmas used to compare int numerals.
-/
prelude
import Leanbin.Init.Data.Int.Order

namespace Int

-- Auxiliary lemmas for proving that to int numerals are different 
-- 1. Lemmas for reducing the problem to the case where the numerals are positive
protected theorem ne_neg_of_ne {a b : ℤ} : a ≠ b → -a ≠ -b := fun h₁ h₂ => absurd (Int.neg_inj h₂) h₁

protected theorem neg_ne_zero_of_ne {a : ℤ} : a ≠ 0 → -a ≠ 0 := fun h₁ h₂ => by
  have : -a = -0 := by
    rwa [Int.neg_zero]
  have : a = 0 := Int.neg_inj this
  contradiction

protected theorem zero_ne_neg_of_ne {a : ℤ} (h : 0 ≠ a) : 0 ≠ -a :=
  Ne.symm (Int.neg_ne_zero_of_ne (Ne.symm h))

protected theorem neg_ne_of_pos {a b : ℤ} : 0 < a → 0 < b → -a ≠ b := fun h₁ h₂ h => by
  rw [← h] at h₂
  change 0 < a at h₁
  have := le_of_ltₓ h₁
  exact absurd (le_of_ltₓ h₁) (not_le_of_gtₓ (Int.neg_of_neg_posₓ h₂))

protected theorem ne_neg_of_pos {a b : ℤ} : 0 < a → 0 < b → a ≠ -b := fun h₁ h₂ => Ne.symm (Int.neg_ne_of_pos h₂ h₁)

-- 2. Lemmas for proving that positive int numerals are nonneg and positive
protected theorem one_pos : 0 < (1 : Int) :=
  Int.zero_lt_oneₓ

protected theorem bit0_pos {a : ℤ} : 0 < a → 0 < bit0 a := fun h => Int.add_posₓ h h

protected theorem bit1_pos {a : ℤ} : 0 ≤ a → 0 < bit1 a := fun h =>
  Int.lt_add_of_le_of_posₓ (Int.add_nonnegₓ h h) Int.zero_lt_oneₓ

protected theorem zero_nonneg : 0 ≤ (0 : ℤ) :=
  le_reflₓ 0

protected theorem one_nonneg : 0 ≤ (1 : ℤ) :=
  le_of_ltₓ Int.zero_lt_oneₓ

protected theorem bit0_nonneg {a : ℤ} : 0 ≤ a → 0 ≤ bit0 a := fun h => Int.add_nonnegₓ h h

protected theorem bit1_nonneg {a : ℤ} : 0 ≤ a → 0 ≤ bit1 a := fun h => le_of_ltₓ (Int.bit1_pos h)

protected theorem nonneg_of_pos {a : ℤ} : 0 < a → 0 ≤ a :=
  le_of_ltₓ

-- 3. nat_abs auxiliary lemmas
theorem neg_succ_of_nat_lt_zero (n : ℕ) : negSucc n < 0 :=
  @Lt.intro _ _ n
    (by
      simp [← neg_succ_of_nat_coe, ← Int.coe_nat_succ, ← Int.coe_nat_add, ← Int.coe_nat_one, ← Int.add_comm, ←
        Int.add_left_comm, ← Int.neg_add, ← Int.add_right_neg, ← Int.zero_add])

theorem zero_le_of_nat (n : ℕ) : 0 ≤ ofNat n :=
  @Le.intro _ _ n
    (by
      rw [Int.zero_add, Int.coe_nat_eq])

theorem of_nat_nat_abs_eq_of_nonneg : ∀ {a : ℤ}, 0 ≤ a → ofNat (natAbs a) = a
  | of_nat n, h => rfl
  | neg_succ_of_nat n, h => absurd (neg_succ_of_nat_lt_zero n) (not_lt_of_geₓ h)

theorem ne_of_nat_abs_ne_nat_abs_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : natAbs a ≠ natAbs b) : a ≠ b :=
  fun h => by
  have : ofNat (natAbs a) = ofNat (natAbs b) := by
    rwa [of_nat_nat_abs_eq_of_nonneg ha, of_nat_nat_abs_eq_of_nonneg hb]
  injection this
  contradiction

protected theorem ne_of_nat_ne_nonneg_case {a b : ℤ} {n m : Nat} (ha : 0 ≤ a) (hb : 0 ≤ b) (e1 : natAbs a = n)
    (e2 : natAbs b = m) (h : n ≠ m) : a ≠ b :=
  have : natAbs a ≠ natAbs b := by
    rwa [e1, e2]
  ne_of_nat_abs_ne_nat_abs_of_nonneg ha hb this

/- 4. Aux lemmas for pushing nat_abs inside numerals
   nat_abs_zero and nat_abs_one are defined at init/data/int/basic.lean -/
theorem nat_abs_of_nat_core (n : ℕ) : natAbs (ofNat n) = n :=
  rfl

theorem nat_abs_of_neg_succ_of_nat (n : ℕ) : natAbs (negSucc n) = Nat.succ n :=
  rfl

protected theorem nat_abs_add_nonneg : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → natAbs (a + b) = natAbs a + natAbs b
  | of_nat n, of_nat m, h₁, h₂ => by
    have : ofNat n + ofNat m = ofNat (n + m) := rfl
    simp [← nat_abs_of_nat_core, ← this]
  | _, neg_succ_of_nat m, h₁, h₂ => absurd (neg_succ_of_nat_lt_zero m) (not_lt_of_geₓ h₂)
  | neg_succ_of_nat n, _, h₁, h₂ => absurd (neg_succ_of_nat_lt_zero n) (not_lt_of_geₓ h₁)

protected theorem nat_abs_add_neg : ∀ {a b : Int}, a < 0 → b < 0 → natAbs (a + b) = natAbs a + natAbs b
  | neg_succ_of_nat n, neg_succ_of_nat m, h₁, h₂ => by
    have : -[1+ n] + -[1+ m] = -[1+ Nat.succ (n + m)] := rfl
    simp [← nat_abs_of_neg_succ_of_nat, ← this, ← Nat.succ_add, ← Nat.add_succ]

protected theorem nat_abs_bit0 : ∀ a : Int, natAbs (bit0 a) = bit0 (natAbs a)
  | of_nat n => Int.nat_abs_add_nonneg (zero_le_of_nat n) (zero_le_of_nat n)
  | neg_succ_of_nat n => Int.nat_abs_add_neg (neg_succ_of_nat_lt_zero n) (neg_succ_of_nat_lt_zero n)

protected theorem nat_abs_bit0_step {a : Int} {n : Nat} (h : natAbs a = n) : natAbs (bit0 a) = bit0 n := by
  rw [← h]
  apply Int.nat_abs_bit0

protected theorem nat_abs_bit1_nonneg {a : Int} (h : 0 ≤ a) : natAbs (bit1 a) = bit1 (natAbs a) :=
  show natAbs (bit0 a + 1) = bit0 (natAbs a) + natAbs 1 by
    rw [Int.nat_abs_add_nonneg (Int.bit0_nonneg h) (le_of_ltₓ Int.zero_lt_oneₓ), Int.nat_abs_bit0]

protected theorem nat_abs_bit1_nonneg_step {a : Int} {n : Nat} (h₁ : 0 ≤ a) (h₂ : natAbs a = n) :
    natAbs (bit1 a) = bit1 n := by
  rw [← h₂]
  apply Int.nat_abs_bit1_nonneg h₁

end Int

