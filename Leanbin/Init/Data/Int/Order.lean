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

def Nonneg (a : ℤ) : Prop :=
  Int.casesOn a (fun n => True) fun n => False

protected def Le (a b : ℤ) : Prop :=
  Nonneg (b - a)

instance : LE Int :=
  ⟨Int.Le⟩

protected def Lt (a b : ℤ) : Prop :=
  a + 1 ≤ b

instance : LT Int :=
  ⟨Int.Lt⟩

def decidableNonneg (a : ℤ) : Decidable (Nonneg a) :=
  Int.casesOn a (fun a => Decidable.true) fun a => Decidable.false

instance decidableLe (a b : ℤ) : Decidable (a ≤ b) :=
  decidableNonneg _

instance decidableLt (a b : ℤ) : Decidable (a < b) :=
  decidableNonneg _

theorem lt_iff_add_one_leₓ (a b : ℤ) : a < b ↔ a + 1 ≤ b :=
  Iff.refl _

theorem Nonneg.elim {a : ℤ} : Nonneg a → ∃ n : ℕ, a = n :=
  Int.casesOn a (fun n H => Exists.introₓ n rfl) fun n' => False.elim

theorem nonneg_or_nonneg_negₓ (a : ℤ) : Nonneg a ∨ Nonneg (-a) :=
  Int.casesOn a (fun n => Or.inl trivialₓ) fun n => Or.inr trivialₓ

theorem Le.intro_sub {a b : ℤ} {n : ℕ} (h : b - a = n) : a ≤ b :=
  show Nonneg (b - a) by
    rw [h] <;> trivial

attribute [local simp]
  Int.sub_eq_add_neg Int.add_assoc Int.add_right_neg Int.add_left_neg Int.zero_add Int.add_zero Int.neg_add Int.neg_neg Int.neg_zero

theorem Le.intro {a b : ℤ} {n : ℕ} (h : a + n = b) : a ≤ b :=
  Le.intro_sub
    (by
      rw [← h, Int.add_comm] <;> simp )

theorem Le.dest_sub {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, b - a = n :=
  Nonneg.elim h

theorem Le.dest {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, a + n = b :=
  match Le.dest_sub h with
  | ⟨n, h₁⟩ =>
    Exists.introₓ n
      (by
        rw [← h₁, Int.add_comm]
        simp )

theorem Le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
  Exists.elim (Le.dest h) h'

protected theorem le_totalₓ (a b : ℤ) : a ≤ b ∨ b ≤ a :=
  Or.imp_rightₓ
    (fun H : Nonneg (-(b - a)) =>
      have : -(b - a) = a - b := by
        simp [Int.add_comm]
      show Nonneg (a - b) from this ▸ H)
    (nonneg_or_nonneg_negₓ (b - a))

theorem coe_nat_le_coe_nat_of_le {m n : ℕ} (h : m ≤ n) : (↑m : ℤ) ≤ ↑n :=
  match Nat.Le.dest h with
  | ⟨k, (hk : m + k = n)⟩ =>
    Le.intro
      (by
        rw [← hk]
        rfl)

theorem le_of_coe_nat_le_coe_nat {m n : ℕ} (h : (↑m : ℤ) ≤ ↑n) : m ≤ n :=
  Le.elim h fun k => fun hk : ↑m + ↑k = ↑n =>
    have : m + k = n := Int.coe_nat_inj ((Int.coe_nat_add m k).trans hk)
    Nat.Le.intro this

theorem coe_nat_le_coe_nat_iff (m n : ℕ) : (↑m : ℤ) ≤ ↑n ↔ m ≤ n :=
  Iff.intro le_of_coe_nat_le_coe_nat coe_nat_le_coe_nat_of_le

theorem coe_zero_le (n : ℕ) : 0 ≤ (↑n : ℤ) :=
  coe_nat_le_coe_nat_of_le n.zero_le

theorem eq_coe_of_zero_le {a : ℤ} (h : 0 ≤ a) : ∃ n : ℕ, a = n := by
  have t := le.dest_sub h
  simp at t
  exact t

theorem eq_succ_of_zero_ltₓ {a : ℤ} (h : 0 < a) : ∃ n : ℕ, a = n.succ :=
  let ⟨n, (h : ↑(1 + n) = a)⟩ := Le.dest h
  ⟨n, by
    rw [Nat.add_comm] at h <;> exact h.symm⟩

theorem lt_add_succₓ (a : ℤ) (n : ℕ) : a < a + ↑(Nat.succ n) :=
  Le.intro
    (show a + 1 + n = a + Nat.succ n by
      simp [Int.coe_nat_eq, Int.add_comm, Int.add_left_comm]
      rfl)

theorem Lt.intro {a b : ℤ} {n : ℕ} (h : a + Nat.succ n = b) : a < b :=
  h ▸ lt_add_succₓ a n

theorem Lt.dest {a b : ℤ} (h : a < b) : ∃ n : ℕ, a + ↑(Nat.succ n) = b :=
  Le.elim h fun n => fun hn : a + 1 + n = b =>
    Exists.introₓ n
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

-- show that the integers form an ordered additive group
protected theorem le_reflₓ (a : ℤ) : a ≤ a :=
  Le.intro (Int.add_zero a)

protected theorem le_transₓ {a b c : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Le.elim h₁ fun n => fun hn : a + n = b =>
    Le.elim h₂ fun m => fun hm : b + m = c => by
      apply le.intro
      rw [← hm, ← hn, Int.add_assoc]
      rfl

protected theorem le_antisymmₓ {a b : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  Le.elim h₁ fun n => fun hn : a + n = b =>
    Le.elim h₂ fun m => fun hm : b + m = a =>
      have : a + ↑(n + m) = a + 0 := by
        rw [Int.coe_nat_add, ← Int.add_assoc, hn, hm, Int.add_zero a]
      have : (↑(n + m) : ℤ) = 0 := Int.add_left_cancel this
      have : n + m = 0 := Int.coe_nat_inj this
      have : n = 0 := Nat.eq_zero_of_add_eq_zero_right this
      show a = b by
        rw [← hn, this, Int.coe_nat_zero, Int.add_zero a]

protected theorem lt_irreflₓ (a : ℤ) : ¬a < a := fun this : a < a =>
  Lt.elim this fun n => fun hn : a + Nat.succ n = a =>
    have : a + Nat.succ n = a + 0 := by
      rw [hn, Int.add_zero]
    have : Nat.succ n = 0 := Int.coe_nat_inj (Int.add_left_cancel this)
    show False from Nat.succ_ne_zero _ this

protected theorem ne_of_ltₓ {a b : ℤ} (h : a < b) : a ≠ b := fun this : a = b =>
  absurd
    (by
      rw [this] at h
      exact h)
    (Int.lt_irreflₓ b)

theorem le_of_ltₓ {a b : ℤ} (h : a < b) : a ≤ b :=
  Lt.elim h fun n => fun hn : a + Nat.succ n = b => Le.intro hn

protected theorem lt_iff_le_and_neₓ (a b : ℤ) : a < b ↔ a ≤ b ∧ a ≠ b :=
  Iff.intro (fun h => ⟨le_of_ltₓ h, Int.ne_of_ltₓ h⟩) fun ⟨aleb, aneb⟩ =>
    Le.elim aleb fun n => fun hn : a + n = b =>
      have : n ≠ 0 := fun this : n = 0 =>
        aneb
          (by
            rw [← hn, this, Int.coe_nat_zero, Int.add_zero])
      have : n = Nat.succ (Nat.pred n) := Eq.symm (Nat.succ_pred_eq_of_posₓ (Nat.pos_of_ne_zeroₓ this))
      Lt.intro
        (by
          rw [this] at hn
          exact hn)

theorem lt_succₓ (a : ℤ) : a < a + 1 :=
  Int.le_reflₓ (a + 1)

protected theorem add_le_add_leftₓ {a b : ℤ} (h : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
  Le.elim h fun n => fun hn : a + n = b =>
    Le.intro
      (show c + a + n = c + b by
        rw [Int.add_assoc, hn])

protected theorem add_lt_add_leftₓ {a b : ℤ} (h : a < b) (c : ℤ) : c + a < c + b :=
  Iff.mpr (Int.lt_iff_le_and_neₓ _ _)
    (And.intro (Int.add_le_add_leftₓ (le_of_ltₓ h) _) fun heq =>
      Int.lt_irreflₓ b
        (by
          rw [Int.add_left_cancel HEq] at h
          exact h))

protected theorem mul_nonnegₓ {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  Le.elim ha fun n => fun hn =>
    Le.elim hb fun m => fun hm =>
      Le.intro
        (show 0 + ↑n * ↑m = a * b by
          rw [← hn, ← hm]
          simp [Int.zero_add])

protected theorem mul_posₓ {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  Lt.elim ha fun n => fun hn =>
    Lt.elim hb fun m => fun hm =>
      Lt.intro
        (show 0 + ↑(Nat.succ (Nat.succ n * m + n)) = a * b by
          rw [← hn, ← hm]
          simp [Int.coe_nat_zero]
          rw [← Int.coe_nat_mul]
          simp [Nat.mul_succ, Nat.add_succ, Nat.succ_add])

protected theorem zero_lt_oneₓ : (0 : ℤ) < 1 :=
  trivialₓ

protected theorem lt_iff_le_not_leₓ {a b : ℤ} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  simp [Int.lt_iff_le_and_neₓ]
  constructor <;> intro h
  · cases' h with hab hn
    constructor
    · assumption
      
    · intro hba
      simp [Int.le_antisymmₓ hab hba] at *
      contradiction
      
    
  · cases' h with hab hn
    constructor
    · assumption
      
    · intro h
      simp_all
      
    

instance : LinearOrderₓ Int where
  le := Int.Le
  le_refl := Int.le_reflₓ
  le_trans := @Int.le_transₓ
  le_antisymm := @Int.le_antisymmₓ
  lt := Int.Lt
  lt_iff_le_not_le := @Int.lt_iff_le_not_leₓ
  le_total := Int.le_totalₓ
  DecidableEq := Int.decidableEq
  decidableLe := Int.decidableLe
  decidableLt := Int.decidableLt

theorem eq_nat_abs_of_zero_le {a : ℤ} (h : 0 ≤ a) : a = natAbs a := by
  let ⟨n, e⟩ := eq_coe_of_zero_le h
  rw [e] <;> rfl

theorem le_nat_abs {a : ℤ} : a ≤ natAbs a :=
  Or.elim (le_totalₓ 0 a)
    (fun h => by
      rw [eq_nat_abs_of_zero_le h] <;> rfl)
    fun h => le_transₓ h (coe_zero_le _)

theorem neg_succ_lt_zeroₓ (n : ℕ) : -[1+ n] < 0 :=
  lt_of_not_geₓ fun h => by
    let ⟨m, h⟩ := eq_coe_of_zero_le h
    contradiction

theorem eq_neg_succ_of_lt_zeroₓ : ∀ {a : ℤ}, a < 0 → ∃ n : ℕ, a = -[1+ n]
  | (n : ℕ), h => absurd h (not_lt_of_geₓ (coe_zero_le _))
  | -[1+ n], h => ⟨n, rfl⟩

-- int is an ordered add comm group
protected theorem eq_neg_of_eq_neg {a b : ℤ} (h : a = -b) : b = -a := by
  rw [h, Int.neg_neg]

protected theorem neg_add_cancel_left (a b : ℤ) : -a + (a + b) = b := by
  rw [← Int.add_assoc, Int.add_left_neg, Int.zero_add]

protected theorem add_neg_cancel_left (a b : ℤ) : a + (-a + b) = b := by
  rw [← Int.add_assoc, Int.add_right_neg, Int.zero_add]

protected theorem add_neg_cancel_right (a b : ℤ) : a + b + -b = a := by
  rw [Int.add_assoc, Int.add_right_neg, Int.add_zero]

protected theorem neg_add_cancel_right (a b : ℤ) : a + -b + b = a := by
  rw [Int.add_assoc, Int.add_left_neg, Int.add_zero]

protected theorem sub_self (a : ℤ) : a - a = 0 := by
  rw [Int.sub_eq_add_neg, Int.add_right_neg]

protected theorem sub_eq_zero_of_eq {a b : ℤ} (h : a = b) : a - b = 0 := by
  rw [h, Int.sub_self]

protected theorem eq_of_sub_eq_zero {a b : ℤ} (h : a - b = 0) : a = b := by
  have : 0 + b = b := by
    rw [Int.zero_add]
  have : a - b + b = b := by
    rwa [h]
  rwa [Int.sub_eq_add_neg, Int.neg_add_cancel_right] at this

protected theorem sub_eq_zero_iff_eq {a b : ℤ} : a - b = 0 ↔ a = b :=
  ⟨Int.eq_of_sub_eq_zero, Int.sub_eq_zero_of_eq⟩

@[simp]
protected theorem neg_eq_of_add_eq_zero {a b : ℤ} (h : a + b = 0) : -a = b := by
  rw [← Int.add_zero (-a), ← h, ← Int.add_assoc, Int.add_left_neg, Int.zero_add]

protected theorem neg_mul_eq_neg_mul (a b : ℤ) : -(a * b) = -a * b :=
  Int.neg_eq_of_add_eq_zero
    (by
      rw [← Int.distrib_right, Int.add_right_neg, Int.zero_mul])

protected theorem neg_mul_eq_mul_neg (a b : ℤ) : -(a * b) = a * -b :=
  Int.neg_eq_of_add_eq_zero
    (by
      rw [← Int.distrib_left, Int.add_right_neg, Int.mul_zero])

theorem neg_mul_eq_neg_mul_symm (a b : ℤ) : -a * b = -(a * b) :=
  Eq.symm (Int.neg_mul_eq_neg_mul a b)

theorem mul_neg_eq_neg_mul_symm (a b : ℤ) : a * -b = -(a * b) :=
  Eq.symm (Int.neg_mul_eq_mul_neg a b)

attribute [local simp] neg_mul_eq_neg_mul_symm mul_neg_eq_neg_mul_symm

protected theorem neg_mul_neg (a b : ℤ) : -a * -b = a * b := by
  simp

protected theorem neg_mul_comm (a b : ℤ) : -a * b = a * -b := by
  simp

protected theorem mul_sub (a b c : ℤ) : a * (b - c) = a * b - a * c :=
  calc
    a * (b - c) = a * b + a * -c := Int.distrib_left a b (-c)
    _ = a * b - a * c := by
      simp
    

protected theorem sub_mul (a b c : ℤ) : (a - b) * c = a * c - b * c :=
  calc
    (a - b) * c = a * c + -b * c := Int.distrib_right a (-b) c
    _ = a * c - b * c := by
      simp
    

section

protected theorem le_of_add_le_add_leftₓ {a b c : ℤ} (h : a + b ≤ a + c) : b ≤ c := by
  have : -a + (a + b) ≤ -a + (a + c) := Int.add_le_add_leftₓ h _
  simp [Int.neg_add_cancel_left] at this
  assumption

protected theorem lt_of_add_lt_add_leftₓ {a b c : ℤ} (h : a + b < a + c) : b < c := by
  have : -a + (a + b) < -a + (a + c) := Int.add_lt_add_leftₓ h _
  simp [Int.neg_add_cancel_left] at this
  assumption

protected theorem add_le_add_rightₓ {a b : ℤ} (h : a ≤ b) (c : ℤ) : a + c ≤ b + c :=
  Int.add_comm c a ▸ Int.add_comm c b ▸ Int.add_le_add_leftₓ h c

protected theorem add_lt_add_rightₓ {a b : ℤ} (h : a < b) (c : ℤ) : a + c < b + c := by
  rw [Int.add_comm a c, Int.add_comm b c]
  exact Int.add_lt_add_leftₓ h c

protected theorem add_le_addₓ {a b c d : ℤ} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  le_transₓ (Int.add_le_add_rightₓ h₁ c) (Int.add_le_add_leftₓ h₂ b)

protected theorem le_add_of_nonneg_rightₓ {a b : ℤ} (h : 0 ≤ b) : a ≤ a + b := by
  have : a + b ≥ a + 0 := Int.add_le_add_leftₓ h a
  rwa [Int.add_zero] at this

protected theorem le_add_of_nonneg_leftₓ {a b : ℤ} (h : 0 ≤ b) : a ≤ b + a := by
  have : 0 + a ≤ b + a := Int.add_le_add_rightₓ h a
  rwa [Int.zero_add] at this

protected theorem add_lt_addₓ {a b c d : ℤ} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  lt_transₓ (Int.add_lt_add_rightₓ h₁ c) (Int.add_lt_add_leftₓ h₂ b)

protected theorem add_lt_add_of_le_of_ltₓ {a b c d : ℤ} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
  lt_of_le_of_ltₓ (Int.add_le_add_rightₓ h₁ c) (Int.add_lt_add_leftₓ h₂ b)

protected theorem add_lt_add_of_lt_of_leₓ {a b c d : ℤ} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_leₓ (Int.add_lt_add_rightₓ h₁ c) (Int.add_le_add_leftₓ h₂ b)

protected theorem lt_add_of_pos_rightₓ (a : ℤ) {b : ℤ} (h : 0 < b) : a < a + b := by
  have : a + 0 < a + b := Int.add_lt_add_leftₓ h a
  rwa [Int.add_zero] at this

protected theorem lt_add_of_pos_leftₓ (a : ℤ) {b : ℤ} (h : 0 < b) : a < b + a := by
  have : 0 + a < b + a := Int.add_lt_add_rightₓ h a
  rwa [Int.zero_add] at this

protected theorem le_of_add_le_add_rightₓ {a b c : ℤ} (h : a + b ≤ c + b) : a ≤ c :=
  Int.le_of_add_le_add_leftₓ
    (show b + a ≤ b + c by
      rw [Int.add_comm b a, Int.add_comm b c]
      assumption)

protected theorem lt_of_add_lt_add_rightₓ {a b c : ℤ} (h : a + b < c + b) : a < c :=
  Int.lt_of_add_lt_add_leftₓ
    (show b + a < b + c by
      rw [Int.add_comm b a, Int.add_comm b c]
      assumption)

-- here we start using properties of zero.
protected theorem add_nonnegₓ {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_le_addₓ ha hb

protected theorem add_posₓ {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_addₓ ha hb

protected theorem add_pos_of_pos_of_nonnegₓ {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_lt_of_leₓ ha hb

protected theorem add_pos_of_nonneg_of_posₓ {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_le_of_ltₓ ha hb

protected theorem add_nonposₓ {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_le_addₓ ha hb

protected theorem add_negₓ {a b : ℤ} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_addₓ ha hb

protected theorem add_neg_of_neg_of_nonposₓ {a b : ℤ} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_lt_of_leₓ ha hb

protected theorem add_neg_of_nonpos_of_negₓ {a b : ℤ} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_le_of_ltₓ ha hb

protected theorem lt_add_of_le_of_posₓ {a b c : ℤ} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
  Int.add_zero b ▸ Int.add_lt_add_of_le_of_ltₓ hbc ha

protected theorem sub_add_cancel (a b : ℤ) : a - b + b = a :=
  Int.neg_add_cancel_right a b

protected theorem add_sub_cancel (a b : ℤ) : a + b - b = a :=
  Int.add_neg_cancel_right a b

protected theorem add_sub_assoc (a b c : ℤ) : a + b - c = a + (b - c) := by
  rw [Int.sub_eq_add_neg, Int.add_assoc, ← Int.sub_eq_add_neg]

protected theorem neg_le_negₓ {a b : ℤ} (h : a ≤ b) : -b ≤ -a := by
  have : 0 ≤ -a + b := Int.add_left_neg a ▸ Int.add_le_add_leftₓ h (-a)
  have : 0 + -b ≤ -a + b + -b := Int.add_le_add_rightₓ this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this

protected theorem le_of_neg_le_negₓ {a b : ℤ} (h : -b ≤ -a) : a ≤ b :=
  suffices - -a ≤ - -b by
    simp [Int.neg_neg] at this
    assumption
  Int.neg_le_negₓ h

protected theorem nonneg_of_neg_nonposₓ {a : ℤ} (h : -a ≤ 0) : 0 ≤ a :=
  have : -a ≤ -0 := by
    rwa [Int.neg_zero]
  Int.le_of_neg_le_negₓ this

protected theorem neg_nonpos_of_nonnegₓ {a : ℤ} (h : 0 ≤ a) : -a ≤ 0 := by
  have : -a ≤ -0 := Int.neg_le_negₓ h
  rwa [Int.neg_zero] at this

protected theorem nonpos_of_neg_nonnegₓ {a : ℤ} (h : 0 ≤ -a) : a ≤ 0 :=
  have : -0 ≤ -a := by
    rwa [Int.neg_zero]
  Int.le_of_neg_le_negₓ this

protected theorem neg_nonneg_of_nonposₓ {a : ℤ} (h : a ≤ 0) : 0 ≤ -a := by
  have : -0 ≤ -a := Int.neg_le_negₓ h
  rwa [Int.neg_zero] at this

protected theorem neg_lt_negₓ {a b : ℤ} (h : a < b) : -b < -a := by
  have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_leftₓ h (-a)
  have : 0 + -b < -a + b + -b := Int.add_lt_add_rightₓ this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this

protected theorem lt_of_neg_lt_negₓ {a b : ℤ} (h : -b < -a) : a < b :=
  Int.neg_neg a ▸ Int.neg_neg b ▸ Int.neg_lt_negₓ h

protected theorem pos_of_neg_negₓ {a : ℤ} (h : -a < 0) : 0 < a :=
  have : -a < -0 := by
    rwa [Int.neg_zero]
  Int.lt_of_neg_lt_negₓ this

protected theorem neg_neg_of_posₓ {a : ℤ} (h : 0 < a) : -a < 0 := by
  have : -a < -0 := Int.neg_lt_negₓ h
  rwa [Int.neg_zero] at this

protected theorem neg_of_neg_posₓ {a : ℤ} (h : 0 < -a) : a < 0 :=
  have : -0 < -a := by
    rwa [Int.neg_zero]
  Int.lt_of_neg_lt_negₓ this

protected theorem neg_pos_of_negₓ {a : ℤ} (h : a < 0) : 0 < -a := by
  have : -0 < -a := Int.neg_lt_negₓ h
  rwa [Int.neg_zero] at this

protected theorem le_neg_of_le_negₓ {a b : ℤ} (h : a ≤ -b) : b ≤ -a := by
  have h := Int.neg_le_negₓ h
  rwa [Int.neg_neg] at h

protected theorem neg_le_of_neg_leₓ {a b : ℤ} (h : -a ≤ b) : -b ≤ a := by
  have h := Int.neg_le_negₓ h
  rwa [Int.neg_neg] at h

protected theorem lt_neg_of_lt_negₓ {a b : ℤ} (h : a < -b) : b < -a := by
  have h := Int.neg_lt_negₓ h
  rwa [Int.neg_neg] at h

protected theorem neg_lt_of_neg_ltₓ {a b : ℤ} (h : -a < b) : -b < a := by
  have h := Int.neg_lt_negₓ h
  rwa [Int.neg_neg] at h

protected theorem sub_nonneg_of_leₓ {a b : ℤ} (h : b ≤ a) : 0 ≤ a - b := by
  have h := Int.add_le_add_rightₓ h (-b)
  rwa [Int.add_right_neg] at h

protected theorem le_of_sub_nonnegₓ {a b : ℤ} (h : 0 ≤ a - b) : b ≤ a := by
  have h := Int.add_le_add_rightₓ h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_nonpos_of_leₓ {a b : ℤ} (h : a ≤ b) : a - b ≤ 0 := by
  have h := Int.add_le_add_rightₓ h (-b)
  rwa [Int.add_right_neg] at h

protected theorem le_of_sub_nonposₓ {a b : ℤ} (h : a - b ≤ 0) : a ≤ b := by
  have h := Int.add_le_add_rightₓ h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_pos_of_ltₓ {a b : ℤ} (h : b < a) : 0 < a - b := by
  have h := Int.add_lt_add_rightₓ h (-b)
  rwa [Int.add_right_neg] at h

protected theorem lt_of_sub_posₓ {a b : ℤ} (h : 0 < a - b) : b < a := by
  have h := Int.add_lt_add_rightₓ h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_neg_of_ltₓ {a b : ℤ} (h : a < b) : a - b < 0 := by
  have h := Int.add_lt_add_rightₓ h (-b)
  rwa [Int.add_right_neg] at h

protected theorem lt_of_sub_negₓ {a b : ℤ} (h : a - b < 0) : a < b := by
  have h := Int.add_lt_add_rightₓ h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem add_le_of_le_neg_addₓ {a b c : ℤ} (h : b ≤ -a + c) : a + b ≤ c := by
  have h := Int.add_le_add_leftₓ h a
  rwa [Int.add_neg_cancel_left] at h

protected theorem le_neg_add_of_add_leₓ {a b c : ℤ} (h : a + b ≤ c) : b ≤ -a + c := by
  have h := Int.add_le_add_leftₓ h (-a)
  rwa [Int.neg_add_cancel_left] at h

protected theorem add_le_of_le_sub_leftₓ {a b c : ℤ} (h : b ≤ c - a) : a + b ≤ c := by
  have h := Int.add_le_add_leftₓ h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h

protected theorem le_sub_left_of_add_leₓ {a b c : ℤ} (h : a + b ≤ c) : b ≤ c - a := by
  have h := Int.add_le_add_rightₓ h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected theorem add_le_of_le_sub_rightₓ {a b c : ℤ} (h : a ≤ c - b) : a + b ≤ c := by
  have h := Int.add_le_add_rightₓ h b
  rwa [Int.sub_add_cancel] at h

protected theorem le_sub_right_of_add_leₓ {a b c : ℤ} (h : a + b ≤ c) : a ≤ c - b := by
  have h := Int.add_le_add_rightₓ h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected theorem le_add_of_neg_add_leₓ {a b c : ℤ} (h : -b + a ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_leftₓ h b
  rwa [Int.add_neg_cancel_left] at h

protected theorem neg_add_le_of_le_addₓ {a b c : ℤ} (h : a ≤ b + c) : -b + a ≤ c := by
  have h := Int.add_le_add_leftₓ h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected theorem le_add_of_sub_left_leₓ {a b c : ℤ} (h : a - b ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_rightₓ h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected theorem sub_left_le_of_le_addₓ {a b c : ℤ} (h : a ≤ b + c) : a - b ≤ c := by
  have h := Int.add_le_add_rightₓ h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected theorem le_add_of_sub_right_leₓ {a b c : ℤ} (h : a - c ≤ b) : a ≤ b + c := by
  have h := Int.add_le_add_rightₓ h c
  rwa [Int.sub_add_cancel] at h

protected theorem sub_right_le_of_le_addₓ {a b c : ℤ} (h : a ≤ b + c) : a - c ≤ b := by
  have h := Int.add_le_add_rightₓ h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected theorem le_add_of_neg_add_le_leftₓ {a b c : ℤ} (h : -b + a ≤ c) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_left_leₓ h

protected theorem neg_add_le_left_of_le_addₓ {a b c : ℤ} (h : a ≤ b + c) : -b + a ≤ c := by
  rw [Int.add_comm]
  exact Int.sub_left_le_of_le_addₓ h

protected theorem le_add_of_neg_add_le_rightₓ {a b c : ℤ} (h : -c + a ≤ b) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_right_leₓ h

protected theorem neg_add_le_right_of_le_addₓ {a b c : ℤ} (h : a ≤ b + c) : -c + a ≤ b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_le_left_of_le_addₓ h

protected theorem le_add_of_neg_le_sub_leftₓ {a b c : ℤ} (h : -a ≤ b - c) : c ≤ a + b :=
  Int.le_add_of_neg_add_le_leftₓ (Int.add_le_of_le_sub_rightₓ h)

protected theorem neg_le_sub_left_of_le_addₓ {a b c : ℤ} (h : c ≤ a + b) : -a ≤ b - c := by
  have h := Int.le_neg_add_of_add_leₓ (Int.sub_left_le_of_le_addₓ h)
  rwa [Int.add_comm] at h

protected theorem le_add_of_neg_le_sub_rightₓ {a b c : ℤ} (h : -b ≤ a - c) : c ≤ a + b :=
  Int.le_add_of_sub_right_leₓ (Int.add_le_of_le_sub_leftₓ h)

protected theorem neg_le_sub_right_of_le_addₓ {a b c : ℤ} (h : c ≤ a + b) : -b ≤ a - c :=
  Int.le_sub_left_of_add_leₓ (Int.sub_right_le_of_le_addₓ h)

protected theorem sub_le_of_sub_leₓ {a b c : ℤ} (h : a - b ≤ c) : a - c ≤ b :=
  Int.sub_left_le_of_le_addₓ (Int.le_add_of_sub_right_leₓ h)

protected theorem sub_le_sub_leftₓ {a b : ℤ} (h : a ≤ b) (c : ℤ) : c - b ≤ c - a :=
  Int.add_le_add_leftₓ (Int.neg_le_negₓ h) c

protected theorem sub_le_sub_rightₓ {a b : ℤ} (h : a ≤ b) (c : ℤ) : a - c ≤ b - c :=
  Int.add_le_add_rightₓ h (-c)

protected theorem sub_le_subₓ {a b c d : ℤ} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  Int.add_le_addₓ hab (Int.neg_le_negₓ hcd)

protected theorem add_lt_of_lt_neg_addₓ {a b c : ℤ} (h : b < -a + c) : a + b < c := by
  have h := Int.add_lt_add_leftₓ h a
  rwa [Int.add_neg_cancel_left] at h

protected theorem lt_neg_add_of_add_ltₓ {a b c : ℤ} (h : a + b < c) : b < -a + c := by
  have h := Int.add_lt_add_leftₓ h (-a)
  rwa [Int.neg_add_cancel_left] at h

protected theorem add_lt_of_lt_sub_leftₓ {a b c : ℤ} (h : b < c - a) : a + b < c := by
  have h := Int.add_lt_add_leftₓ h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h

protected theorem lt_sub_left_of_add_ltₓ {a b c : ℤ} (h : a + b < c) : b < c - a := by
  have h := Int.add_lt_add_rightₓ h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected theorem add_lt_of_lt_sub_rightₓ {a b c : ℤ} (h : a < c - b) : a + b < c := by
  have h := Int.add_lt_add_rightₓ h b
  rwa [Int.sub_add_cancel] at h

protected theorem lt_sub_right_of_add_ltₓ {a b c : ℤ} (h : a + b < c) : a < c - b := by
  have h := Int.add_lt_add_rightₓ h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected theorem lt_add_of_neg_add_ltₓ {a b c : ℤ} (h : -b + a < c) : a < b + c := by
  have h := Int.add_lt_add_leftₓ h b
  rwa [Int.add_neg_cancel_left] at h

protected theorem neg_add_lt_of_lt_addₓ {a b c : ℤ} (h : a < b + c) : -b + a < c := by
  have h := Int.add_lt_add_leftₓ h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected theorem lt_add_of_sub_left_ltₓ {a b c : ℤ} (h : a - b < c) : a < b + c := by
  have h := Int.add_lt_add_rightₓ h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected theorem sub_left_lt_of_lt_addₓ {a b c : ℤ} (h : a < b + c) : a - b < c := by
  have h := Int.add_lt_add_rightₓ h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected theorem lt_add_of_sub_right_ltₓ {a b c : ℤ} (h : a - c < b) : a < b + c := by
  have h := Int.add_lt_add_rightₓ h c
  rwa [Int.sub_add_cancel] at h

protected theorem sub_right_lt_of_lt_addₓ {a b c : ℤ} (h : a < b + c) : a - c < b := by
  have h := Int.add_lt_add_rightₓ h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected theorem lt_add_of_neg_add_lt_leftₓ {a b c : ℤ} (h : -b + a < c) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_left_ltₓ h

protected theorem neg_add_lt_left_of_lt_addₓ {a b c : ℤ} (h : a < b + c) : -b + a < c := by
  rw [Int.add_comm]
  exact Int.sub_left_lt_of_lt_addₓ h

protected theorem lt_add_of_neg_add_lt_rightₓ {a b c : ℤ} (h : -c + a < b) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_right_ltₓ h

protected theorem neg_add_lt_right_of_lt_addₓ {a b c : ℤ} (h : a < b + c) : -c + a < b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_lt_left_of_lt_addₓ h

protected theorem lt_add_of_neg_lt_sub_leftₓ {a b c : ℤ} (h : -a < b - c) : c < a + b :=
  Int.lt_add_of_neg_add_lt_leftₓ (Int.add_lt_of_lt_sub_rightₓ h)

protected theorem neg_lt_sub_left_of_lt_addₓ {a b c : ℤ} (h : c < a + b) : -a < b - c := by
  have h := Int.lt_neg_add_of_add_ltₓ (Int.sub_left_lt_of_lt_addₓ h)
  rwa [Int.add_comm] at h

protected theorem lt_add_of_neg_lt_sub_rightₓ {a b c : ℤ} (h : -b < a - c) : c < a + b :=
  Int.lt_add_of_sub_right_ltₓ (Int.add_lt_of_lt_sub_leftₓ h)

protected theorem neg_lt_sub_right_of_lt_addₓ {a b c : ℤ} (h : c < a + b) : -b < a - c :=
  Int.lt_sub_left_of_add_ltₓ (Int.sub_right_lt_of_lt_addₓ h)

protected theorem sub_lt_of_sub_ltₓ {a b c : ℤ} (h : a - b < c) : a - c < b :=
  Int.sub_left_lt_of_lt_addₓ (Int.lt_add_of_sub_right_ltₓ h)

protected theorem sub_lt_sub_leftₓ {a b : ℤ} (h : a < b) (c : ℤ) : c - b < c - a :=
  Int.add_lt_add_leftₓ (Int.neg_lt_negₓ h) c

protected theorem sub_lt_sub_rightₓ {a b : ℤ} (h : a < b) (c : ℤ) : a - c < b - c :=
  Int.add_lt_add_rightₓ h (-c)

protected theorem sub_lt_subₓ {a b c d : ℤ} (hab : a < b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_addₓ hab (Int.neg_lt_negₓ hcd)

protected theorem sub_lt_sub_of_le_of_ltₓ {a b c d : ℤ} (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_add_of_le_of_ltₓ hab (Int.neg_lt_negₓ hcd)

protected theorem sub_lt_sub_of_lt_of_leₓ {a b c d : ℤ} (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
  Int.add_lt_add_of_lt_of_leₓ hab (Int.neg_le_negₓ hcd)

protected theorem sub_le_selfₓ (a : ℤ) {b : ℤ} (h : 0 ≤ b) : a - b ≤ a :=
  calc
    a - b = a + -b := rfl
    _ ≤ a + 0 := Int.add_le_add_leftₓ (Int.neg_nonpos_of_nonnegₓ h) _
    _ = a := by
      rw [Int.add_zero]
    

protected theorem sub_lt_selfₓ (a : ℤ) {b : ℤ} (h : 0 < b) : a - b < a :=
  calc
    a - b = a + -b := rfl
    _ < a + 0 := Int.add_lt_add_leftₓ (Int.neg_neg_of_posₓ h) _
    _ = a := by
      rw [Int.add_zero]
    

protected theorem add_le_add_threeₓ {a b c d e f : ℤ} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a + b + c ≤ d + e + f :=
  by
  apply le_transₓ
  apply Int.add_le_addₓ
  apply Int.add_le_addₓ
  assumption'
  apply le_reflₓ

end

-- missing facts
protected theorem mul_lt_mul_of_pos_leftₓ {a b c : ℤ} (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b := by
  have : 0 < b - a := Int.sub_pos_of_ltₓ h₁
  have : 0 < c * (b - a) := Int.mul_posₓ h₂ this
  rw [Int.mul_sub] at this
  exact Int.lt_of_sub_posₓ this

protected theorem mul_lt_mul_of_pos_rightₓ {a b c : ℤ} (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c := by
  have : 0 < b - a := Int.sub_pos_of_ltₓ h₁
  have : 0 < (b - a) * c := Int.mul_posₓ this h₂
  rw [Int.sub_mul] at this
  exact Int.lt_of_sub_posₓ this

protected theorem mul_le_mul_of_nonneg_leftₓ {a b c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b := by
  by_cases' hba : b ≤ a
  · simp [le_antisymmₓ hba h₁]
    
  by_cases' hc0 : c ≤ 0
  · simp [le_antisymmₓ hc0 h₂, Int.zero_mul]
    
  exact (le_not_le_of_ltₓ (Int.mul_lt_mul_of_pos_leftₓ (lt_of_le_not_leₓ h₁ hba) (lt_of_le_not_leₓ h₂ hc0))).left

protected theorem mul_le_mul_of_nonneg_rightₓ {a b c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c := by
  by_cases' hba : b ≤ a
  · simp [le_antisymmₓ hba h₁]
    
  by_cases' hc0 : c ≤ 0
  · simp [le_antisymmₓ hc0 h₂, Int.mul_zero]
    
  exact (le_not_le_of_ltₓ (Int.mul_lt_mul_of_pos_rightₓ (lt_of_le_not_leₓ h₁ hba) (lt_of_le_not_leₓ h₂ hc0))).left

-- TODO: there are four variations, depending on which variables we assume to be nonneg
protected theorem mul_le_mulₓ {a b c d : ℤ} (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d :=
  calc
    a * b ≤ c * b := Int.mul_le_mul_of_nonneg_rightₓ hac nn_b
    _ ≤ c * d := Int.mul_le_mul_of_nonneg_leftₓ hbd nn_c
    

protected theorem mul_nonpos_of_nonneg_of_nonposₓ {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  have h : a * b ≤ a * 0 := Int.mul_le_mul_of_nonneg_leftₓ hb ha
  rwa [Int.mul_zero] at h

protected theorem mul_nonpos_of_nonpos_of_nonnegₓ {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  have h : a * b ≤ 0 * b := Int.mul_le_mul_of_nonneg_rightₓ ha hb
  rwa [Int.zero_mul] at h

protected theorem mul_lt_mulₓ {a b c d : ℤ} (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b) (nn_c : 0 ≤ c) :
    a * b < c * d :=
  calc
    a * b < c * b := Int.mul_lt_mul_of_pos_rightₓ hac pos_b
    _ ≤ c * d := Int.mul_le_mul_of_nonneg_leftₓ hbd nn_c
    

protected theorem mul_lt_mul'ₓ {a b c d : ℤ} (h1 : a ≤ c) (h2 : b < d) (h3 : 0 ≤ b) (h4 : 0 < c) : a * b < c * d :=
  calc
    a * b ≤ c * b := Int.mul_le_mul_of_nonneg_rightₓ h1 h3
    _ < c * d := Int.mul_lt_mul_of_pos_leftₓ h2 h4
    

protected theorem mul_neg_of_pos_of_negₓ {a b : ℤ} (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  have h : a * b < a * 0 := Int.mul_lt_mul_of_pos_leftₓ hb ha
  rwa [Int.mul_zero] at h

protected theorem mul_neg_of_neg_of_posₓ {a b : ℤ} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have h : a * b < 0 * b := Int.mul_lt_mul_of_pos_rightₓ ha hb
  rwa [Int.zero_mul] at h

protected theorem mul_le_mul_of_nonpos_rightₓ {a b c : ℤ} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
  have : -c ≥ 0 := Int.neg_nonneg_of_nonposₓ hc
  have : b * -c ≤ a * -c := Int.mul_le_mul_of_nonneg_rightₓ h this
  have : -(b * c) ≤ -(a * c) := by
    rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this
  Int.le_of_neg_le_negₓ this

protected theorem mul_nonneg_of_nonpos_of_nonposₓ {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  have : 0 * b ≤ a * b := Int.mul_le_mul_of_nonpos_rightₓ ha hb
  rwa [Int.zero_mul] at this

protected theorem mul_lt_mul_of_neg_leftₓ {a b c : ℤ} (h : b < a) (hc : c < 0) : c * a < c * b :=
  have : -c > 0 := Int.neg_pos_of_negₓ hc
  have : -c * b < -c * a := Int.mul_lt_mul_of_pos_leftₓ h this
  have : -(c * b) < -(c * a) := by
    rwa [← Int.neg_mul_eq_neg_mul, ← Int.neg_mul_eq_neg_mul] at this
  Int.lt_of_neg_lt_negₓ this

protected theorem mul_lt_mul_of_neg_rightₓ {a b c : ℤ} (h : b < a) (hc : c < 0) : a * c < b * c :=
  have : -c > 0 := Int.neg_pos_of_negₓ hc
  have : b * -c < a * -c := Int.mul_lt_mul_of_pos_rightₓ h this
  have : -(b * c) < -(a * c) := by
    rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this
  Int.lt_of_neg_lt_negₓ this

protected theorem mul_pos_of_neg_of_negₓ {a b : ℤ} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have : 0 * b < a * b := Int.mul_lt_mul_of_neg_rightₓ ha hb
  rwa [Int.zero_mul] at this

protected theorem mul_self_le_mul_selfₓ {a b : ℤ} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
  Int.mul_le_mulₓ h2 h2 h1 (le_transₓ h1 h2)

protected theorem mul_self_lt_mul_selfₓ {a b : ℤ} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  Int.mul_lt_mul'ₓ (le_of_ltₓ h2) h2 h1 (lt_of_le_of_ltₓ h1 h2)

-- more facts specific to int
theorem of_nat_nonneg (n : ℕ) : 0 ≤ ofNat n :=
  trivialₓ

theorem coe_succ_pos (n : Nat) : 0 < (Nat.succ n : ℤ) :=
  coe_nat_lt_coe_nat_of_lt (Nat.succ_posₓ _)

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : ∃ n : ℕ, a = -n :=
  let ⟨n, h⟩ := eq_coe_of_zero_le (Int.neg_nonneg_of_nonposₓ H)
  ⟨n, Int.eq_neg_of_eq_neg h.symm⟩

theorem nat_abs_of_nonneg {a : ℤ} (H : 0 ≤ a) : (natAbs a : ℤ) = a :=
  match a, eq_coe_of_zero_le H with
  | _, ⟨n, rfl⟩ => rfl

theorem of_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : (natAbs a : ℤ) = -a := by
  rw [← nat_abs_neg, nat_abs_of_nonneg (Int.neg_nonneg_of_nonposₓ H)]

theorem lt_of_add_one_leₓ {a b : ℤ} (H : a + 1 ≤ b) : a < b :=
  H

theorem add_one_le_of_ltₓ {a b : ℤ} (H : a < b) : a + 1 ≤ b :=
  H

theorem lt_add_one_of_leₓ {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
  Int.add_le_add_rightₓ H 1

theorem le_of_lt_add_oneₓ {a b : ℤ} (H : a < b + 1) : a ≤ b :=
  Int.le_of_add_le_add_rightₓ H

theorem sub_one_lt_of_leₓ {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
  Int.sub_right_lt_of_lt_addₓ <| lt_add_one_of_leₓ H

theorem le_of_sub_one_ltₓ {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
  le_of_lt_add_one <| Int.lt_add_of_sub_right_ltₓ H

theorem le_sub_one_of_ltₓ {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
  Int.le_sub_right_of_add_leₓ H

theorem lt_of_le_sub_oneₓ {a b : ℤ} (H : a ≤ b - 1) : a < b :=
  Int.add_le_of_le_sub_rightₓ H

theorem sign_of_succ (n : Nat) : sign (Nat.succ n) = 1 :=
  rfl

theorem sign_eq_one_of_posₓ {a : ℤ} (h : 0 < a) : sign a = 1 :=
  match a, eq_succ_of_zero_ltₓ h with
  | _, ⟨n, rfl⟩ => rfl

theorem sign_eq_neg_one_of_negₓ {a : ℤ} (h : a < 0) : sign a = -1 :=
  match a, eq_neg_succ_of_lt_zeroₓ h with
  | _, ⟨n, rfl⟩ => rfl

theorem eq_zero_of_sign_eq_zero : ∀ {a : ℤ}, sign a = 0 → a = 0
  | 0, _ => rfl

theorem pos_of_sign_eq_oneₓ : ∀ {a : ℤ}, sign a = 1 → 0 < a
  | (n + 1 : ℕ), _ => coe_nat_lt_coe_nat_of_lt (Nat.succ_posₓ _)

theorem neg_of_sign_eq_neg_oneₓ : ∀ {a : ℤ}, sign a = -1 → a < 0
  | (n + 1 : ℕ), h => nomatch h
  | 0, h => nomatch h
  | -[1+ n], _ => neg_succ_lt_zeroₓ _

theorem sign_eq_one_iff_posₓ (a : ℤ) : sign a = 1 ↔ 0 < a :=
  ⟨pos_of_sign_eq_oneₓ, sign_eq_one_of_posₓ⟩

theorem sign_eq_neg_one_iff_negₓ (a : ℤ) : sign a = -1 ↔ a < 0 :=
  ⟨neg_of_sign_eq_neg_oneₓ, sign_eq_neg_one_of_negₓ⟩

theorem sign_eq_zero_iff_zero (a : ℤ) : sign a = 0 ↔ a = 0 :=
  ⟨eq_zero_of_sign_eq_zero, fun h => by
    rw [h, sign_zero]⟩

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  match lt_trichotomyₓ 0 a with
  | Or.inl hlt₁ =>
    match lt_trichotomyₓ 0 b with
    | Or.inl hlt₂ => by
      have : 0 < a * b := Int.mul_posₓ hlt₁ hlt₂
      rw [h] at this
      exact absurd this (lt_irreflₓ _)
    | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
    | Or.inr (Or.inr hgt₂) => by
      have : 0 > a * b := Int.mul_neg_of_pos_of_negₓ hlt₁ hgt₂
      rw [h] at this
      exact absurd this (lt_irreflₓ _)
  | Or.inr (Or.inl heq₁) => Or.inl heq₁.symm
  | Or.inr (Or.inr hgt₁) =>
    match lt_trichotomyₓ 0 b with
    | Or.inl hlt₂ => by
      have : 0 > a * b := Int.mul_neg_of_neg_of_posₓ hgt₁ hlt₂
      rw [h] at this
      exact absurd this (lt_irreflₓ _)
    | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
    | Or.inr (Or.inr hgt₂) => by
      have : 0 < a * b := Int.mul_pos_of_neg_of_negₓ hgt₁ hgt₂
      rw [h] at this
      exact absurd this (lt_irreflₓ _)

protected theorem eq_of_mul_eq_mul_right {a b c : ℤ} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have : b * a - c * a = 0 := Int.sub_eq_zero_of_eq h
  have : (b - c) * a = 0 := by
    rw [Int.sub_mul, this]
  have : b - c = 0 := (Int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha
  Int.eq_of_sub_eq_zero this

protected theorem eq_of_mul_eq_mul_left {a b c : ℤ} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have : a * b - a * c = 0 := Int.sub_eq_zero_of_eq h
  have : a * (b - c) = 0 := by
    rw [Int.mul_sub, this]
  have : b - c = 0 := (Int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha
  Int.eq_of_sub_eq_zero this

theorem eq_one_of_mul_eq_self_left {a b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
  Int.eq_of_mul_eq_mul_right Hpos
    (by
      rw [Int.one_mul, H])

theorem eq_one_of_mul_eq_self_right {a b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
  Int.eq_of_mul_eq_mul_left Hpos
    (by
      rw [Int.mul_one, H])

end Int

