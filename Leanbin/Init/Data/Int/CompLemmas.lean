prelude
import Leanbin.Init.Data.Int.Order

namespace Int

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

theorem neg_succ_of_nat_lt_zero (n : ℕ) : neg_succ_of_nat n < 0 :=
  @lt.intro _ _ n
    (by
      simp [neg_succ_of_nat_coe, Int.coe_nat_succ, Int.coe_nat_add, Int.coe_nat_one, Int.add_comm, Int.add_left_comm,
        Int.neg_add, Int.add_right_neg, Int.zero_add])

theorem zero_le_of_nat (n : ℕ) : 0 ≤ of_nat n :=
  @le.intro _ _ n
    (by
      rw [Int.zero_add, Int.coe_nat_eq])

theorem of_nat_nat_abs_eq_of_nonneg : ∀ {a : ℤ}, 0 ≤ a → of_nat (nat_abs a) = a
  | of_nat n, h => rfl
  | neg_succ_of_nat n, h => absurd (neg_succ_of_nat_lt_zero n) (not_lt_of_geₓ h)

theorem ne_of_nat_abs_ne_nat_abs_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : nat_abs a ≠ nat_abs b) : a ≠ b :=
  fun h => by
  have : of_nat (nat_abs a) = of_nat (nat_abs b) := by
    rwa [of_nat_nat_abs_eq_of_nonneg ha, of_nat_nat_abs_eq_of_nonneg hb]
  injection this
  contradiction

protected theorem ne_of_nat_ne_nonneg_case {a b : ℤ} {n m : Nat} (ha : 0 ≤ a) (hb : 0 ≤ b) (e1 : nat_abs a = n)
    (e2 : nat_abs b = m) (h : n ≠ m) : a ≠ b :=
  have : nat_abs a ≠ nat_abs b := by
    rwa [e1, e2]
  ne_of_nat_abs_ne_nat_abs_of_nonneg ha hb this

theorem nat_abs_of_nat_core (n : ℕ) : nat_abs (of_nat n) = n :=
  rfl

theorem nat_abs_of_neg_succ_of_nat (n : ℕ) : nat_abs (neg_succ_of_nat n) = Nat.succ n :=
  rfl

protected theorem nat_abs_add_nonneg : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → nat_abs (a + b) = nat_abs a + nat_abs b
  | of_nat n, of_nat m, h₁, h₂ => by
    have : of_nat n + of_nat m = of_nat (n + m) := rfl
    simp [nat_abs_of_nat_core, this]
  | _, neg_succ_of_nat m, h₁, h₂ => absurd (neg_succ_of_nat_lt_zero m) (not_lt_of_geₓ h₂)
  | neg_succ_of_nat n, _, h₁, h₂ => absurd (neg_succ_of_nat_lt_zero n) (not_lt_of_geₓ h₁)

protected theorem nat_abs_add_neg : ∀ {a b : Int}, a < 0 → b < 0 → nat_abs (a + b) = nat_abs a + nat_abs b
  | neg_succ_of_nat n, neg_succ_of_nat m, h₁, h₂ => by
    have : -[1+ n] + -[1+ m] = -[1+ Nat.succ (n + m)] := rfl
    simp [nat_abs_of_neg_succ_of_nat, this, Nat.succ_add, Nat.add_succ]

protected theorem nat_abs_bit0 : ∀ a : Int, nat_abs (bit0 a) = bit0 (nat_abs a)
  | of_nat n => Int.nat_abs_add_nonneg (zero_le_of_nat n) (zero_le_of_nat n)
  | neg_succ_of_nat n => Int.nat_abs_add_neg (neg_succ_of_nat_lt_zero n) (neg_succ_of_nat_lt_zero n)

protected theorem nat_abs_bit0_step {a : Int} {n : Nat} (h : nat_abs a = n) : nat_abs (bit0 a) = bit0 n := by
  rw [← h]
  apply Int.nat_abs_bit0

protected theorem nat_abs_bit1_nonneg {a : Int} (h : 0 ≤ a) : nat_abs (bit1 a) = bit1 (nat_abs a) :=
  show nat_abs (bit0 a + 1) = bit0 (nat_abs a) + nat_abs 1 by
    rw [Int.nat_abs_add_nonneg (Int.bit0_nonneg h) (le_of_ltₓ Int.zero_lt_oneₓ), Int.nat_abs_bit0]

protected theorem nat_abs_bit1_nonneg_step {a : Int} {n : Nat} (h₁ : 0 ≤ a) (h₂ : nat_abs a = n) :
    nat_abs (bit1 a) = bit1 n := by
  rw [← h₂]
  apply Int.nat_abs_bit1_nonneg h₁

end Int

