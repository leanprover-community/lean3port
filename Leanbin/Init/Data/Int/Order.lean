/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers.

! This file was ported from Lean 3 source module init.data.int.order
! leanprover-community/lean commit 4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Int.Basic
import Leanbin.Init.Data.Ordering.Basic

namespace Int

#print Int.NonNeg /-
def NonNeg (a : ℤ) : Prop :=
  Int.casesOn a (fun n => True) fun n => False
#align int.nonneg Int.NonNeg
-/

#print Int.le /-
protected def le (a b : ℤ) : Prop :=
  NonNeg (b - a)
#align int.le Int.le
-/

instance : LE Int :=
  ⟨Int.le⟩

#print Int.lt /-
protected def lt (a b : ℤ) : Prop :=
  a + 1 ≤ b
#align int.lt Int.lt
-/

instance : LT Int :=
  ⟨Int.lt⟩

#print Int.decNonneg /-
def decNonneg (a : ℤ) : Decidable (NonNeg a) :=
  Int.casesOn a (fun a => decidableTrue) fun a => decidableFalse
#align int.decidable_nonneg Int.decNonneg
-/

#print Int.decLe /-
instance decLe (a b : ℤ) : Decidable (a ≤ b) :=
  decNonneg _
#align int.decidable_le Int.decLe
-/

#print Int.decLt /-
instance decLt (a b : ℤ) : Decidable (a < b) :=
  decNonneg _
#align int.decidable_lt Int.decLt
-/

#print Int.lt_iff_add_one_le /-
theorem lt_iff_add_one_le (a b : ℤ) : a < b ↔ a + 1 ≤ b :=
  Iff.refl _
#align int.lt_iff_add_one_le Int.lt_iff_add_one_le
-/

#print Int.NonNeg.elim /-
theorem NonNeg.elim {a : ℤ} : NonNeg a → ∃ n : ℕ, a = n :=
  Int.casesOn a (fun n H => Exists.intro n rfl) fun n' => False.elim
#align int.nonneg.elim Int.NonNeg.elim
-/

theorem nonNeg_or_nonNeg_neg (a : ℤ) : NonNeg a ∨ NonNeg (-a) :=
  Int.casesOn a (fun n => Or.inl trivial) fun n => Or.inr trivial
#align int.nonneg_or_nonneg_neg Int.nonNeg_or_nonNeg_neg

#print Int.le.intro_sub /-
theorem le.intro_sub {a b : ℤ} {n : ℕ} (h : b - a = n) : a ≤ b :=
  show NonNeg (b - a) by rw [h] <;> trivial
#align int.le.intro_sub Int.le.intro_sub
-/

attribute [local simp] Int.sub_eq_add_neg Int.add_assoc Int.add_right_neg Int.add_left_neg
  Int.zero_add Int.add_zero Int.neg_add Int.neg_neg Int.neg_zero

#print Int.le.intro /-
theorem le.intro {a b : ℤ} {n : ℕ} (h : a + n = b) : a ≤ b :=
  le.intro_sub (by rw [← h, Int.add_comm] <;> simp)
#align int.le.intro Int.le.intro
-/

#print Int.le.dest_sub /-
theorem le.dest_sub {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, b - a = n :=
  NonNeg.elim h
#align int.le.dest_sub Int.le.dest_sub
-/

#print Int.le.dest /-
theorem le.dest {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, a + n = b :=
  match le.dest_sub h with
  | ⟨n, h₁⟩ => Exists.intro n (by rw [← h₁, Int.add_comm]; simp)
#align int.le.dest Int.le.dest
-/

#print Int.le.elim /-
theorem le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
  Exists.elim (le.dest h) h'
#align int.le.elim Int.le.elim
-/

#print Int.le_total /-
protected theorem le_total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
  Or.imp_right
    (fun H : NonNeg (-(b - a)) =>
      have : -(b - a) = a - b := by simp [Int.add_comm]
      show NonNeg (a - b) from this ▸ H)
    (nonNeg_or_nonNeg_neg (b - a))
#align int.le_total Int.le_total
-/

#print Int.ofNat_le_ofNat_of_le /-
theorem ofNat_le_ofNat_of_le {m n : ℕ} (h : m ≤ n) : (↑m : ℤ) ≤ ↑n :=
  match Nat.le.dest h with
  | ⟨k, (hk : m + k = n)⟩ => le.intro (by rw [← hk]; rfl)
#align int.coe_nat_le_coe_nat_of_le Int.ofNat_le_ofNat_of_le
-/

#print Int.le_of_ofNat_le_ofNat /-
theorem le_of_ofNat_le_ofNat {m n : ℕ} (h : (↑m : ℤ) ≤ ↑n) : m ≤ n :=
  le.elim h fun k => fun hk : ↑m + ↑k = ↑n =>
    have : m + k = n := Int.ofNat.inj ((Int.ofNat_add m k).trans hk)
    Nat.le.intro this
#align int.le_of_coe_nat_le_coe_nat Int.le_of_ofNat_le_ofNat
-/

#print Int.ofNat_le /-
theorem ofNat_le (m n : ℕ) : (↑m : ℤ) ≤ ↑n ↔ m ≤ n :=
  Iff.intro le_of_ofNat_le_ofNat ofNat_le_ofNat_of_le
#align int.coe_nat_le_coe_nat_iff Int.ofNat_le
-/

#print Int.ofNat_zero_le /-
theorem ofNat_zero_le (n : ℕ) : 0 ≤ (↑n : ℤ) :=
  ofNat_le_ofNat_of_le n.zero_le
#align int.coe_zero_le Int.ofNat_zero_le
-/

#print Int.eq_ofNat_of_zero_le /-
theorem eq_ofNat_of_zero_le {a : ℤ} (h : 0 ≤ a) : ∃ n : ℕ, a = n := by have t := le.dest_sub h;
  simp at t ; exact t
#align int.eq_coe_of_zero_le Int.eq_ofNat_of_zero_le
-/

#print Int.eq_succ_of_zero_lt /-
theorem eq_succ_of_zero_lt {a : ℤ} (h : 0 < a) : ∃ n : ℕ, a = n.succ :=
  let ⟨n, (h : ↑(1 + n) = a)⟩ := le.dest h
  ⟨n, by rw [Nat.add_comm] at h  <;> exact h.symm⟩
#align int.eq_succ_of_zero_lt Int.eq_succ_of_zero_lt
-/

#print Int.lt_add_succ /-
theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + ↑(Nat.succ n) :=
  le.intro
    (show a + 1 + n = a + Nat.succ n by simp [Int.coe_nat_eq, Int.add_comm, Int.add_left_comm]; rfl)
#align int.lt_add_succ Int.lt_add_succ
-/

#print Int.lt.intro /-
theorem lt.intro {a b : ℤ} {n : ℕ} (h : a + Nat.succ n = b) : a < b :=
  h ▸ lt_add_succ a n
#align int.lt.intro Int.lt.intro
-/

#print Int.lt.dest /-
theorem lt.dest {a b : ℤ} (h : a < b) : ∃ n : ℕ, a + ↑(Nat.succ n) = b :=
  le.elim h fun n => fun hn : a + 1 + n = b =>
    Exists.intro n (by rw [← hn, Int.add_assoc, Int.add_comm 1]; rfl)
#align int.lt.dest Int.lt.dest
-/

#print Int.lt.elim /-
theorem lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(Nat.succ n) = b → P) : P :=
  Exists.elim (lt.dest h) h'
#align int.lt.elim Int.lt.elim
-/

#print Int.ofNat_lt /-
theorem ofNat_lt (n m : ℕ) : (↑n : ℤ) < ↑m ↔ n < m := by
  rw [lt_iff_add_one_le, ← Int.ofNat_succ, coe_nat_le_coe_nat_iff]; rfl
#align int.coe_nat_lt_coe_nat_iff Int.ofNat_lt
-/

#print Int.lt_of_ofNat_lt_ofNat /-
theorem lt_of_ofNat_lt_ofNat {m n : ℕ} (h : (↑m : ℤ) < ↑n) : m < n :=
  (ofNat_lt _ _).mp h
#align int.lt_of_coe_nat_lt_coe_nat Int.lt_of_ofNat_lt_ofNat
-/

#print Int.ofNat_lt_ofNat_of_lt /-
theorem ofNat_lt_ofNat_of_lt {m n : ℕ} (h : m < n) : (↑m : ℤ) < ↑n :=
  (ofNat_lt _ _).mpr h
#align int.coe_nat_lt_coe_nat_of_lt Int.ofNat_lt_ofNat_of_lt
-/

/-! show that the integers form an ordered additive group -/


#print Int.le_refl /-
protected theorem le_refl (a : ℤ) : a ≤ a :=
  le.intro (Int.add_zero a)
#align int.le_refl Int.le_refl
-/

#print Int.le_trans /-
protected theorem le_trans {a b c : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  le.elim h₁ fun n => fun hn : a + n = b =>
    le.elim h₂ fun m => fun hm : b + m = c => by apply le.intro; rw [← hm, ← hn, Int.add_assoc]; rfl
#align int.le_trans Int.le_trans
-/

#print Int.le_antisymm /-
protected theorem le_antisymm {a b : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  le.elim h₁ fun n => fun hn : a + n = b =>
    le.elim h₂ fun m => fun hm : b + m = a =>
      have : a + ↑(n + m) = a + 0 := by rw [Int.ofNat_add, ← Int.add_assoc, hn, hm, Int.add_zero a]
      have : (↑(n + m) : ℤ) = 0 := Int.add_left_cancel this
      have : n + m = 0 := Int.ofNat.inj this
      have : n = 0 := Nat.eq_zero_of_add_eq_zero_right this
      show a = b by rw [← hn, this, Int.ofNat_zero, Int.add_zero a]
#align int.le_antisymm Int.le_antisymm
-/

#print Int.lt_irrefl /-
protected theorem lt_irrefl (a : ℤ) : ¬a < a := fun this : a < a =>
  lt.elim this fun n => fun hn : a + Nat.succ n = a =>
    have : a + Nat.succ n = a + 0 := by rw [hn, Int.add_zero]
    have : Nat.succ n = 0 := Int.ofNat.inj (Int.add_left_cancel this)
    show False from Nat.succ_ne_zero _ this
#align int.lt_irrefl Int.lt_irrefl
-/

#print Int.ne_of_lt /-
protected theorem ne_of_lt {a b : ℤ} (h : a < b) : a ≠ b := fun this : a = b =>
  absurd (by rw [this] at h ; exact h) (Int.lt_irrefl b)
#align int.ne_of_lt Int.ne_of_lt
-/

#print Int.le_of_lt /-
theorem le_of_lt {a b : ℤ} (h : a < b) : a ≤ b :=
  lt.elim h fun n => fun hn : a + Nat.succ n = b => le.intro hn
#align int.le_of_lt Int.le_of_lt
-/

#print Int.lt_iff_le_and_ne /-
protected theorem lt_iff_le_and_ne (a b : ℤ) : a < b ↔ a ≤ b ∧ a ≠ b :=
  Iff.intro (fun h => ⟨le_of_lt h, Int.ne_of_lt h⟩) fun ⟨aleb, aneb⟩ =>
    le.elim aleb fun n => fun hn : a + n = b =>
      have : n ≠ 0 := fun this : n = 0 => aneb (by rw [← hn, this, Int.ofNat_zero, Int.add_zero])
      have : n = Nat.succ (Nat.pred n) :=
        Eq.symm (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero this))
      lt.intro (by rw [this] at hn ; exact hn)
#align int.lt_iff_le_and_ne Int.lt_iff_le_and_ne
-/

#print Int.lt_succ /-
theorem lt_succ (a : ℤ) : a < a + 1 :=
  Int.le_refl (a + 1)
#align int.lt_succ Int.lt_succ
-/

#print Int.add_le_add_left /-
protected theorem add_le_add_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
  le.elim h fun n => fun hn : a + n = b =>
    le.intro (show c + a + n = c + b by rw [Int.add_assoc, hn])
#align int.add_le_add_left Int.add_le_add_left
-/

#print Int.add_lt_add_left /-
protected theorem add_lt_add_left {a b : ℤ} (h : a < b) (c : ℤ) : c + a < c + b :=
  Iff.mpr (Int.lt_iff_le_and_ne _ _)
    (And.intro (Int.add_le_add_left (le_of_lt h) _) fun heq =>
      Int.lt_irrefl b (by rw [Int.add_left_cancel HEq] at h ; exact h))
#align int.add_lt_add_left Int.add_lt_add_left
-/

#print Int.mul_nonneg /-
protected theorem mul_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  le.elim ha fun n => fun hn =>
    le.elim hb fun m => fun hm =>
      le.intro (show 0 + ↑n * ↑m = a * b by rw [← hn, ← hm]; simp [Int.zero_add])
#align int.mul_nonneg Int.mul_nonneg
-/

#print Int.mul_pos /-
protected theorem mul_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  lt.elim ha fun n => fun hn =>
    lt.elim hb fun m => fun hm =>
      lt.intro
        (show 0 + ↑(Nat.succ (Nat.succ n * m + n)) = a * b
          by
          rw [← hn, ← hm]; simp [Int.ofNat_zero]
          rw [← Int.ofNat_mul]; simp [Nat.mul_succ, Nat.add_succ, Nat.succ_add])
#align int.mul_pos Int.mul_pos
-/

#print Int.zero_lt_one /-
protected theorem zero_lt_one : (0 : ℤ) < 1 :=
  trivial
#align int.zero_lt_one Int.zero_lt_one
-/

#print Int.lt_iff_le_not_le /-
protected theorem lt_iff_le_not_le {a b : ℤ} : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  by
  simp [Int.lt_iff_le_and_ne]; constructor <;> intro h
  · cases' h with hab hn; constructor
    · assumption
    · intro hba; simp [Int.le_antisymm hab hba] at *; contradiction
  · cases' h with hab hn; constructor
    · assumption
    · intro h; simp_all
#align int.lt_iff_le_not_le Int.lt_iff_le_not_le
-/

instance : LinearOrder Int where
  le := Int.le
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt := Int.lt
  lt_iff_le_not_le := @Int.lt_iff_le_not_le
  le_total := Int.le_total
  DecidableEq := Int.decidableEq
  decidableLe := Int.decLe
  decidableLt := Int.decLt

#print Int.eq_natAbs_of_zero_le /-
theorem eq_natAbs_of_zero_le {a : ℤ} (h : 0 ≤ a) : a = natAbs a :=
  by
  let ⟨n, e⟩ := eq_ofNat_of_zero_le h
  rw [e] <;> rfl
#align int.eq_nat_abs_of_zero_le Int.eq_natAbs_of_zero_le
-/

#print Int.le_natAbs /-
theorem le_natAbs {a : ℤ} : a ≤ natAbs a :=
  Or.elim (le_total 0 a) (fun h => by rw [eq_nat_abs_of_zero_le h] <;> rfl) fun h =>
    le_trans h (ofNat_zero_le _)
#align int.le_nat_abs Int.le_natAbs
-/

#print Int.negSucc_lt_zero /-
theorem negSucc_lt_zero (n : ℕ) : -[n+1] < 0 :=
  lt_of_not_ge fun h => by
    let ⟨m, h⟩ := eq_ofNat_of_zero_le h
    contradiction
#align int.neg_succ_lt_zero Int.negSucc_lt_zero
-/

#print Int.eq_negSucc_of_lt_zero /-
theorem eq_negSucc_of_lt_zero : ∀ {a : ℤ}, a < 0 → ∃ n : ℕ, a = -[n+1]
  | (n : ℕ), h => absurd h (not_lt_of_ge (ofNat_zero_le _))
  | -[n+1], h => ⟨n, rfl⟩
#align int.eq_neg_succ_of_lt_zero Int.eq_negSucc_of_lt_zero
-/

/-! int is an ordered add comm group -/


#print Int.eq_neg_of_eq_neg /-
protected theorem eq_neg_of_eq_neg {a b : ℤ} (h : a = -b) : b = -a := by rw [h, Int.neg_neg]
#align int.eq_neg_of_eq_neg Int.eq_neg_of_eq_neg
-/

#print Int.neg_add_cancel_left /-
protected theorem neg_add_cancel_left (a b : ℤ) : -a + (a + b) = b := by
  rw [← Int.add_assoc, Int.add_left_neg, Int.zero_add]
#align int.neg_add_cancel_left Int.neg_add_cancel_left
-/

#print Int.add_neg_cancel_left /-
protected theorem add_neg_cancel_left (a b : ℤ) : a + (-a + b) = b := by
  rw [← Int.add_assoc, Int.add_right_neg, Int.zero_add]
#align int.add_neg_cancel_left Int.add_neg_cancel_left
-/

#print Int.add_neg_cancel_right /-
protected theorem add_neg_cancel_right (a b : ℤ) : a + b + -b = a := by
  rw [Int.add_assoc, Int.add_right_neg, Int.add_zero]
#align int.add_neg_cancel_right Int.add_neg_cancel_right
-/

#print Int.neg_add_cancel_right /-
protected theorem neg_add_cancel_right (a b : ℤ) : a + -b + b = a := by
  rw [Int.add_assoc, Int.add_left_neg, Int.add_zero]
#align int.neg_add_cancel_right Int.neg_add_cancel_right
-/

#print Int.sub_self /-
protected theorem sub_self (a : ℤ) : a - a = 0 := by rw [Int.sub_eq_add_neg, Int.add_right_neg]
#align int.sub_self Int.sub_self
-/

#print Int.sub_eq_zero_of_eq /-
protected theorem sub_eq_zero_of_eq {a b : ℤ} (h : a = b) : a - b = 0 := by rw [h, Int.sub_self]
#align int.sub_eq_zero_of_eq Int.sub_eq_zero_of_eq
-/

#print Int.eq_of_sub_eq_zero /-
protected theorem eq_of_sub_eq_zero {a b : ℤ} (h : a - b = 0) : a = b :=
  by
  have : 0 + b = b := by rw [Int.zero_add]
  have : a - b + b = b := by rwa [h]
  rwa [Int.sub_eq_add_neg, Int.neg_add_cancel_right] at this 
#align int.eq_of_sub_eq_zero Int.eq_of_sub_eq_zero
-/

#print Int.sub_eq_zero /-
protected theorem sub_eq_zero {a b : ℤ} : a - b = 0 ↔ a = b :=
  ⟨Int.eq_of_sub_eq_zero, Int.sub_eq_zero_of_eq⟩
#align int.sub_eq_zero_iff_eq Int.sub_eq_zero
-/

#print Int.neg_eq_of_add_eq_zero /-
@[simp]
protected theorem neg_eq_of_add_eq_zero {a b : ℤ} (h : a + b = 0) : -a = b := by
  rw [← Int.add_zero (-a), ← h, ← Int.add_assoc, Int.add_left_neg, Int.zero_add]
#align int.neg_eq_of_add_eq_zero Int.neg_eq_of_add_eq_zero
-/

#print Int.neg_mul_eq_neg_mul /-
protected theorem neg_mul_eq_neg_mul (a b : ℤ) : -(a * b) = -a * b :=
  Int.neg_eq_of_add_eq_zero (by rw [← Int.add_mul, Int.add_right_neg, Int.zero_mul])
#align int.neg_mul_eq_neg_mul Int.neg_mul_eq_neg_mul
-/

#print Int.neg_mul_eq_mul_neg /-
protected theorem neg_mul_eq_mul_neg (a b : ℤ) : -(a * b) = a * -b :=
  Int.neg_eq_of_add_eq_zero (by rw [← Int.mul_add, Int.add_right_neg, Int.mul_zero])
#align int.neg_mul_eq_mul_neg Int.neg_mul_eq_mul_neg
-/

#print Int.neg_mul_eq_neg_mul_symm /-
theorem neg_mul_eq_neg_mul_symm (a b : ℤ) : -a * b = -(a * b) :=
  Eq.symm (Int.neg_mul_eq_neg_mul a b)
#align int.neg_mul_eq_neg_mul_symm Int.neg_mul_eq_neg_mul_symm
-/

#print Int.mul_neg_eq_neg_mul_symm /-
theorem mul_neg_eq_neg_mul_symm (a b : ℤ) : a * -b = -(a * b) :=
  Eq.symm (Int.neg_mul_eq_mul_neg a b)
#align int.mul_neg_eq_neg_mul_symm Int.mul_neg_eq_neg_mul_symm
-/

attribute [local simp] neg_mul_eq_neg_mul_symm mul_neg_eq_neg_mul_symm

#print Int.neg_mul_neg /-
protected theorem neg_mul_neg (a b : ℤ) : -a * -b = a * b := by simp
#align int.neg_mul_neg Int.neg_mul_neg
-/

#print Int.neg_mul_comm /-
protected theorem neg_mul_comm (a b : ℤ) : -a * b = a * -b := by simp
#align int.neg_mul_comm Int.neg_mul_comm
-/

#print Int.mul_sub /-
protected theorem mul_sub (a b c : ℤ) : a * (b - c) = a * b - a * c :=
  calc
    a * (b - c) = a * b + a * -c := Int.mul_add a b (-c)
    _ = a * b - a * c := by simp
#align int.mul_sub Int.mul_sub
-/

#print Int.sub_mul /-
protected theorem sub_mul (a b c : ℤ) : (a - b) * c = a * c - b * c :=
  calc
    (a - b) * c = a * c + -b * c := Int.add_mul a (-b) c
    _ = a * c - b * c := by simp
#align int.sub_mul Int.sub_mul
-/

section

#print Int.le_of_add_le_add_left /-
protected theorem le_of_add_le_add_left {a b c : ℤ} (h : a + b ≤ a + c) : b ≤ c :=
  by
  have : -a + (a + b) ≤ -a + (a + c) := Int.add_le_add_left h _
  simp [Int.neg_add_cancel_left] at this 
  assumption
#align int.le_of_add_le_add_left Int.le_of_add_le_add_left
-/

#print Int.lt_of_add_lt_add_left /-
protected theorem lt_of_add_lt_add_left {a b c : ℤ} (h : a + b < a + c) : b < c :=
  by
  have : -a + (a + b) < -a + (a + c) := Int.add_lt_add_left h _
  simp [Int.neg_add_cancel_left] at this 
  assumption
#align int.lt_of_add_lt_add_left Int.lt_of_add_lt_add_left
-/

#print Int.add_le_add_right /-
protected theorem add_le_add_right {a b : ℤ} (h : a ≤ b) (c : ℤ) : a + c ≤ b + c :=
  Int.add_comm c a ▸ Int.add_comm c b ▸ Int.add_le_add_left h c
#align int.add_le_add_right Int.add_le_add_right
-/

#print Int.add_lt_add_right /-
protected theorem add_lt_add_right {a b : ℤ} (h : a < b) (c : ℤ) : a + c < b + c :=
  by
  rw [Int.add_comm a c, Int.add_comm b c]
  exact Int.add_lt_add_left h c
#align int.add_lt_add_right Int.add_lt_add_right
-/

#print Int.add_le_add /-
protected theorem add_le_add {a b c d : ℤ} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  le_trans (Int.add_le_add_right h₁ c) (Int.add_le_add_left h₂ b)
#align int.add_le_add Int.add_le_add
-/

#print Int.le_add_of_nonneg_right /-
protected theorem le_add_of_nonneg_right {a b : ℤ} (h : 0 ≤ b) : a ≤ a + b :=
  by
  have : a + b ≥ a + 0 := Int.add_le_add_left h a
  rwa [Int.add_zero] at this 
#align int.le_add_of_nonneg_right Int.le_add_of_nonneg_right
-/

#print Int.le_add_of_nonneg_left /-
protected theorem le_add_of_nonneg_left {a b : ℤ} (h : 0 ≤ b) : a ≤ b + a :=
  by
  have : 0 + a ≤ b + a := Int.add_le_add_right h a
  rwa [Int.zero_add] at this 
#align int.le_add_of_nonneg_left Int.le_add_of_nonneg_left
-/

#print Int.add_lt_add /-
protected theorem add_lt_add {a b c d : ℤ} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  lt_trans (Int.add_lt_add_right h₁ c) (Int.add_lt_add_left h₂ b)
#align int.add_lt_add Int.add_lt_add
-/

#print Int.add_lt_add_of_le_of_lt /-
protected theorem add_lt_add_of_le_of_lt {a b c d : ℤ} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
  lt_of_le_of_lt (Int.add_le_add_right h₁ c) (Int.add_lt_add_left h₂ b)
#align int.add_lt_add_of_le_of_lt Int.add_lt_add_of_le_of_lt
-/

#print Int.add_lt_add_of_lt_of_le /-
protected theorem add_lt_add_of_lt_of_le {a b c d : ℤ} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (Int.add_lt_add_right h₁ c) (Int.add_le_add_left h₂ b)
#align int.add_lt_add_of_lt_of_le Int.add_lt_add_of_lt_of_le
-/

#print Int.lt_add_of_pos_right /-
protected theorem lt_add_of_pos_right (a : ℤ) {b : ℤ} (h : 0 < b) : a < a + b :=
  by
  have : a + 0 < a + b := Int.add_lt_add_left h a
  rwa [Int.add_zero] at this 
#align int.lt_add_of_pos_right Int.lt_add_of_pos_right
-/

#print Int.lt_add_of_pos_left /-
protected theorem lt_add_of_pos_left (a : ℤ) {b : ℤ} (h : 0 < b) : a < b + a :=
  by
  have : 0 + a < b + a := Int.add_lt_add_right h a
  rwa [Int.zero_add] at this 
#align int.lt_add_of_pos_left Int.lt_add_of_pos_left
-/

#print Int.le_of_add_le_add_right /-
protected theorem le_of_add_le_add_right {a b c : ℤ} (h : a + b ≤ c + b) : a ≤ c :=
  Int.le_of_add_le_add_left
    (show b + a ≤ b + c by rw [Int.add_comm b a, Int.add_comm b c]; assumption)
#align int.le_of_add_le_add_right Int.le_of_add_le_add_right
-/

#print Int.lt_of_add_lt_add_right /-
protected theorem lt_of_add_lt_add_right {a b c : ℤ} (h : a + b < c + b) : a < c :=
  Int.lt_of_add_lt_add_left
    (show b + a < b + c by rw [Int.add_comm b a, Int.add_comm b c]; assumption)
#align int.lt_of_add_lt_add_right Int.lt_of_add_lt_add_right
-/

#print Int.add_nonneg /-
-- here we start using properties of zero.
protected theorem add_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_le_add ha hb
#align int.add_nonneg Int.add_nonneg
-/

#print Int.add_pos /-
protected theorem add_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add ha hb
#align int.add_pos Int.add_pos
-/

#print Int.add_pos_of_pos_of_nonneg /-
protected theorem add_pos_of_pos_of_nonneg {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_lt_of_le ha hb
#align int.add_pos_of_pos_of_nonneg Int.add_pos_of_pos_of_nonneg
-/

#print Int.add_pos_of_nonneg_of_pos /-
protected theorem add_pos_of_nonneg_of_pos {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_le_of_lt ha hb
#align int.add_pos_of_nonneg_of_pos Int.add_pos_of_nonneg_of_pos
-/

#print Int.add_nonpos /-
protected theorem add_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_le_add ha hb
#align int.add_nonpos Int.add_nonpos
-/

#print Int.add_neg /-
protected theorem add_neg {a b : ℤ} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add ha hb
#align int.add_neg Int.add_neg
-/

#print Int.add_neg_of_neg_of_nonpos /-
protected theorem add_neg_of_neg_of_nonpos {a b : ℤ} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_lt_of_le ha hb
#align int.add_neg_of_neg_of_nonpos Int.add_neg_of_neg_of_nonpos
-/

#print Int.add_neg_of_nonpos_of_neg /-
protected theorem add_neg_of_nonpos_of_neg {a b : ℤ} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_le_of_lt ha hb
#align int.add_neg_of_nonpos_of_neg Int.add_neg_of_nonpos_of_neg
-/

#print Int.lt_add_of_le_of_pos /-
protected theorem lt_add_of_le_of_pos {a b c : ℤ} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
  Int.add_zero b ▸ Int.add_lt_add_of_le_of_lt hbc ha
#align int.lt_add_of_le_of_pos Int.lt_add_of_le_of_pos
-/

#print Int.sub_add_cancel /-
protected theorem sub_add_cancel (a b : ℤ) : a - b + b = a :=
  Int.neg_add_cancel_right a b
#align int.sub_add_cancel Int.sub_add_cancel
-/

#print Int.add_sub_cancel /-
protected theorem add_sub_cancel (a b : ℤ) : a + b - b = a :=
  Int.add_neg_cancel_right a b
#align int.add_sub_cancel Int.add_sub_cancel
-/

#print Int.add_sub_assoc /-
protected theorem add_sub_assoc (a b c : ℤ) : a + b - c = a + (b - c) := by
  rw [Int.sub_eq_add_neg, Int.add_assoc, ← Int.sub_eq_add_neg]
#align int.add_sub_assoc Int.add_sub_assoc
-/

#print Int.neg_le_neg /-
protected theorem neg_le_neg {a b : ℤ} (h : a ≤ b) : -b ≤ -a :=
  by
  have : 0 ≤ -a + b := Int.add_left_neg a ▸ Int.add_le_add_left h (-a)
  have : 0 + -b ≤ -a + b + -b := Int.add_le_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this 
#align int.neg_le_neg Int.neg_le_neg
-/

#print Int.le_of_neg_le_neg /-
protected theorem le_of_neg_le_neg {a b : ℤ} (h : -b ≤ -a) : a ≤ b :=
  suffices - -a ≤ - -b by simp [Int.neg_neg] at this ; assumption
  Int.neg_le_neg h
#align int.le_of_neg_le_neg Int.le_of_neg_le_neg
-/

#print Int.nonneg_of_neg_nonpos /-
protected theorem nonneg_of_neg_nonpos {a : ℤ} (h : -a ≤ 0) : 0 ≤ a :=
  have : -a ≤ -0 := by rwa [Int.neg_zero]
  Int.le_of_neg_le_neg this
#align int.nonneg_of_neg_nonpos Int.nonneg_of_neg_nonpos
-/

#print Int.neg_nonpos_of_nonneg /-
protected theorem neg_nonpos_of_nonneg {a : ℤ} (h : 0 ≤ a) : -a ≤ 0 :=
  by
  have : -a ≤ -0 := Int.neg_le_neg h
  rwa [Int.neg_zero] at this 
#align int.neg_nonpos_of_nonneg Int.neg_nonpos_of_nonneg
-/

#print Int.nonpos_of_neg_nonneg /-
protected theorem nonpos_of_neg_nonneg {a : ℤ} (h : 0 ≤ -a) : a ≤ 0 :=
  have : -0 ≤ -a := by rwa [Int.neg_zero]
  Int.le_of_neg_le_neg this
#align int.nonpos_of_neg_nonneg Int.nonpos_of_neg_nonneg
-/

#print Int.neg_nonneg_of_nonpos /-
protected theorem neg_nonneg_of_nonpos {a : ℤ} (h : a ≤ 0) : 0 ≤ -a :=
  by
  have : -0 ≤ -a := Int.neg_le_neg h
  rwa [Int.neg_zero] at this 
#align int.neg_nonneg_of_nonpos Int.neg_nonneg_of_nonpos
-/

#print Int.neg_lt_neg /-
protected theorem neg_lt_neg {a b : ℤ} (h : a < b) : -b < -a :=
  by
  have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_left h (-a)
  have : 0 + -b < -a + b + -b := Int.add_lt_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this 
#align int.neg_lt_neg Int.neg_lt_neg
-/

#print Int.lt_of_neg_lt_neg /-
protected theorem lt_of_neg_lt_neg {a b : ℤ} (h : -b < -a) : a < b :=
  Int.neg_neg a ▸ Int.neg_neg b ▸ Int.neg_lt_neg h
#align int.lt_of_neg_lt_neg Int.lt_of_neg_lt_neg
-/

#print Int.pos_of_neg_neg /-
protected theorem pos_of_neg_neg {a : ℤ} (h : -a < 0) : 0 < a :=
  have : -a < -0 := by rwa [Int.neg_zero]
  Int.lt_of_neg_lt_neg this
#align int.pos_of_neg_neg Int.pos_of_neg_neg
-/

#print Int.neg_neg_of_pos /-
protected theorem neg_neg_of_pos {a : ℤ} (h : 0 < a) : -a < 0 :=
  by
  have : -a < -0 := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this 
#align int.neg_neg_of_pos Int.neg_neg_of_pos
-/

#print Int.neg_of_neg_pos /-
protected theorem neg_of_neg_pos {a : ℤ} (h : 0 < -a) : a < 0 :=
  have : -0 < -a := by rwa [Int.neg_zero]
  Int.lt_of_neg_lt_neg this
#align int.neg_of_neg_pos Int.neg_of_neg_pos
-/

#print Int.neg_pos_of_neg /-
protected theorem neg_pos_of_neg {a : ℤ} (h : a < 0) : 0 < -a :=
  by
  have : -0 < -a := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this 
#align int.neg_pos_of_neg Int.neg_pos_of_neg
-/

#print Int.le_neg_of_le_neg /-
protected theorem le_neg_of_le_neg {a b : ℤ} (h : a ≤ -b) : b ≤ -a :=
  by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h 
#align int.le_neg_of_le_neg Int.le_neg_of_le_neg
-/

#print Int.neg_le_of_neg_le /-
protected theorem neg_le_of_neg_le {a b : ℤ} (h : -a ≤ b) : -b ≤ a :=
  by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h 
#align int.neg_le_of_neg_le Int.neg_le_of_neg_le
-/

#print Int.lt_neg_of_lt_neg /-
protected theorem lt_neg_of_lt_neg {a b : ℤ} (h : a < -b) : b < -a :=
  by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h 
#align int.lt_neg_of_lt_neg Int.lt_neg_of_lt_neg
-/

#print Int.neg_lt_of_neg_lt /-
protected theorem neg_lt_of_neg_lt {a b : ℤ} (h : -a < b) : -b < a :=
  by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h 
#align int.neg_lt_of_neg_lt Int.neg_lt_of_neg_lt
-/

#print Int.sub_nonneg_of_le /-
protected theorem sub_nonneg_of_le {a b : ℤ} (h : b ≤ a) : 0 ≤ a - b :=
  by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h 
#align int.sub_nonneg_of_le Int.sub_nonneg_of_le
-/

#print Int.le_of_sub_nonneg /-
protected theorem le_of_sub_nonneg {a b : ℤ} (h : 0 ≤ a - b) : b ≤ a :=
  by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h 
#align int.le_of_sub_nonneg Int.le_of_sub_nonneg
-/

#print Int.sub_nonpos_of_le /-
protected theorem sub_nonpos_of_le {a b : ℤ} (h : a ≤ b) : a - b ≤ 0 :=
  by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h 
#align int.sub_nonpos_of_le Int.sub_nonpos_of_le
-/

#print Int.le_of_sub_nonpos /-
protected theorem le_of_sub_nonpos {a b : ℤ} (h : a - b ≤ 0) : a ≤ b :=
  by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h 
#align int.le_of_sub_nonpos Int.le_of_sub_nonpos
-/

#print Int.sub_pos_of_lt /-
protected theorem sub_pos_of_lt {a b : ℤ} (h : b < a) : 0 < a - b :=
  by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h 
#align int.sub_pos_of_lt Int.sub_pos_of_lt
-/

#print Int.lt_of_sub_pos /-
protected theorem lt_of_sub_pos {a b : ℤ} (h : 0 < a - b) : b < a :=
  by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h 
#align int.lt_of_sub_pos Int.lt_of_sub_pos
-/

#print Int.sub_neg_of_lt /-
protected theorem sub_neg_of_lt {a b : ℤ} (h : a < b) : a - b < 0 :=
  by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h 
#align int.sub_neg_of_lt Int.sub_neg_of_lt
-/

#print Int.lt_of_sub_neg /-
protected theorem lt_of_sub_neg {a b : ℤ} (h : a - b < 0) : a < b :=
  by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h 
#align int.lt_of_sub_neg Int.lt_of_sub_neg
-/

#print Int.add_le_of_le_neg_add /-
protected theorem add_le_of_le_neg_add {a b c : ℤ} (h : b ≤ -a + c) : a + b ≤ c :=
  by
  have h := Int.add_le_add_left h a
  rwa [Int.add_neg_cancel_left] at h 
#align int.add_le_of_le_neg_add Int.add_le_of_le_neg_add
-/

#print Int.le_neg_add_of_add_le /-
protected theorem le_neg_add_of_add_le {a b c : ℤ} (h : a + b ≤ c) : b ≤ -a + c :=
  by
  have h := Int.add_le_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h 
#align int.le_neg_add_of_add_le Int.le_neg_add_of_add_le
-/

#print Int.add_le_of_le_sub_left /-
protected theorem add_le_of_le_sub_left {a b c : ℤ} (h : b ≤ c - a) : a + b ≤ c :=
  by
  have h := Int.add_le_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h 
#align int.add_le_of_le_sub_left Int.add_le_of_le_sub_left
-/

#print Int.le_sub_left_of_add_le /-
protected theorem le_sub_left_of_add_le {a b c : ℤ} (h : a + b ≤ c) : b ≤ c - a :=
  by
  have h := Int.add_le_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h 
#align int.le_sub_left_of_add_le Int.le_sub_left_of_add_le
-/

#print Int.add_le_of_le_sub_right /-
protected theorem add_le_of_le_sub_right {a b c : ℤ} (h : a ≤ c - b) : a + b ≤ c :=
  by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel] at h 
#align int.add_le_of_le_sub_right Int.add_le_of_le_sub_right
-/

#print Int.le_sub_right_of_add_le /-
protected theorem le_sub_right_of_add_le {a b c : ℤ} (h : a + b ≤ c) : a ≤ c - b :=
  by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h 
#align int.le_sub_right_of_add_le Int.le_sub_right_of_add_le
-/

#print Int.le_add_of_neg_add_le /-
protected theorem le_add_of_neg_add_le {a b c : ℤ} (h : -b + a ≤ c) : a ≤ b + c :=
  by
  have h := Int.add_le_add_left h b
  rwa [Int.add_neg_cancel_left] at h 
#align int.le_add_of_neg_add_le Int.le_add_of_neg_add_le
-/

#print Int.neg_add_le_of_le_add /-
protected theorem neg_add_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -b + a ≤ c :=
  by
  have h := Int.add_le_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h 
#align int.neg_add_le_of_le_add Int.neg_add_le_of_le_add
-/

#print Int.le_add_of_sub_left_le /-
protected theorem le_add_of_sub_left_le {a b c : ℤ} (h : a - b ≤ c) : a ≤ b + c :=
  by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h 
#align int.le_add_of_sub_left_le Int.le_add_of_sub_left_le
-/

#print Int.sub_left_le_of_le_add /-
protected theorem sub_left_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : a - b ≤ c :=
  by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h 
#align int.sub_left_le_of_le_add Int.sub_left_le_of_le_add
-/

#print Int.le_add_of_sub_right_le /-
protected theorem le_add_of_sub_right_le {a b c : ℤ} (h : a - c ≤ b) : a ≤ b + c :=
  by
  have h := Int.add_le_add_right h c
  rwa [Int.sub_add_cancel] at h 
#align int.le_add_of_sub_right_le Int.le_add_of_sub_right_le
-/

#print Int.sub_right_le_of_le_add /-
protected theorem sub_right_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : a - c ≤ b :=
  by
  have h := Int.add_le_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h 
#align int.sub_right_le_of_le_add Int.sub_right_le_of_le_add
-/

#print Int.le_add_of_neg_add_le_left /-
protected theorem le_add_of_neg_add_le_left {a b c : ℤ} (h : -b + a ≤ c) : a ≤ b + c :=
  by
  rw [Int.add_comm] at h 
  exact Int.le_add_of_sub_left_le h
#align int.le_add_of_neg_add_le_left Int.le_add_of_neg_add_le_left
-/

#print Int.neg_add_le_left_of_le_add /-
protected theorem neg_add_le_left_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -b + a ≤ c :=
  by
  rw [Int.add_comm]
  exact Int.sub_left_le_of_le_add h
#align int.neg_add_le_left_of_le_add Int.neg_add_le_left_of_le_add
-/

#print Int.le_add_of_neg_add_le_right /-
protected theorem le_add_of_neg_add_le_right {a b c : ℤ} (h : -c + a ≤ b) : a ≤ b + c :=
  by
  rw [Int.add_comm] at h 
  exact Int.le_add_of_sub_right_le h
#align int.le_add_of_neg_add_le_right Int.le_add_of_neg_add_le_right
-/

#print Int.neg_add_le_right_of_le_add /-
protected theorem neg_add_le_right_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -c + a ≤ b :=
  by
  rw [Int.add_comm] at h 
  exact Int.neg_add_le_left_of_le_add h
#align int.neg_add_le_right_of_le_add Int.neg_add_le_right_of_le_add
-/

#print Int.le_add_of_neg_le_sub_left /-
protected theorem le_add_of_neg_le_sub_left {a b c : ℤ} (h : -a ≤ b - c) : c ≤ a + b :=
  Int.le_add_of_neg_add_le_left (Int.add_le_of_le_sub_right h)
#align int.le_add_of_neg_le_sub_left Int.le_add_of_neg_le_sub_left
-/

#print Int.neg_le_sub_left_of_le_add /-
protected theorem neg_le_sub_left_of_le_add {a b c : ℤ} (h : c ≤ a + b) : -a ≤ b - c :=
  by
  have h := Int.le_neg_add_of_add_le (Int.sub_left_le_of_le_add h)
  rwa [Int.add_comm] at h 
#align int.neg_le_sub_left_of_le_add Int.neg_le_sub_left_of_le_add
-/

#print Int.le_add_of_neg_le_sub_right /-
protected theorem le_add_of_neg_le_sub_right {a b c : ℤ} (h : -b ≤ a - c) : c ≤ a + b :=
  Int.le_add_of_sub_right_le (Int.add_le_of_le_sub_left h)
#align int.le_add_of_neg_le_sub_right Int.le_add_of_neg_le_sub_right
-/

#print Int.neg_le_sub_right_of_le_add /-
protected theorem neg_le_sub_right_of_le_add {a b c : ℤ} (h : c ≤ a + b) : -b ≤ a - c :=
  Int.le_sub_left_of_add_le (Int.sub_right_le_of_le_add h)
#align int.neg_le_sub_right_of_le_add Int.neg_le_sub_right_of_le_add
-/

#print Int.sub_le_of_sub_le /-
protected theorem sub_le_of_sub_le {a b c : ℤ} (h : a - b ≤ c) : a - c ≤ b :=
  Int.sub_left_le_of_le_add (Int.le_add_of_sub_right_le h)
#align int.sub_le_of_sub_le Int.sub_le_of_sub_le
-/

#print Int.sub_le_sub_left /-
protected theorem sub_le_sub_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c - b ≤ c - a :=
  Int.add_le_add_left (Int.neg_le_neg h) c
#align int.sub_le_sub_left Int.sub_le_sub_left
-/

#print Int.sub_le_sub_right /-
protected theorem sub_le_sub_right {a b : ℤ} (h : a ≤ b) (c : ℤ) : a - c ≤ b - c :=
  Int.add_le_add_right h (-c)
#align int.sub_le_sub_right Int.sub_le_sub_right
-/

#print Int.sub_le_sub /-
protected theorem sub_le_sub {a b c d : ℤ} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  Int.add_le_add hab (Int.neg_le_neg hcd)
#align int.sub_le_sub Int.sub_le_sub
-/

#print Int.add_lt_of_lt_neg_add /-
protected theorem add_lt_of_lt_neg_add {a b c : ℤ} (h : b < -a + c) : a + b < c :=
  by
  have h := Int.add_lt_add_left h a
  rwa [Int.add_neg_cancel_left] at h 
#align int.add_lt_of_lt_neg_add Int.add_lt_of_lt_neg_add
-/

#print Int.lt_neg_add_of_add_lt /-
protected theorem lt_neg_add_of_add_lt {a b c : ℤ} (h : a + b < c) : b < -a + c :=
  by
  have h := Int.add_lt_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h 
#align int.lt_neg_add_of_add_lt Int.lt_neg_add_of_add_lt
-/

#print Int.add_lt_of_lt_sub_left /-
protected theorem add_lt_of_lt_sub_left {a b c : ℤ} (h : b < c - a) : a + b < c :=
  by
  have h := Int.add_lt_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h 
#align int.add_lt_of_lt_sub_left Int.add_lt_of_lt_sub_left
-/

#print Int.lt_sub_left_of_add_lt /-
protected theorem lt_sub_left_of_add_lt {a b c : ℤ} (h : a + b < c) : b < c - a :=
  by
  have h := Int.add_lt_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h 
#align int.lt_sub_left_of_add_lt Int.lt_sub_left_of_add_lt
-/

#print Int.add_lt_of_lt_sub_right /-
protected theorem add_lt_of_lt_sub_right {a b c : ℤ} (h : a < c - b) : a + b < c :=
  by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel] at h 
#align int.add_lt_of_lt_sub_right Int.add_lt_of_lt_sub_right
-/

#print Int.lt_sub_right_of_add_lt /-
protected theorem lt_sub_right_of_add_lt {a b c : ℤ} (h : a + b < c) : a < c - b :=
  by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h 
#align int.lt_sub_right_of_add_lt Int.lt_sub_right_of_add_lt
-/

#print Int.lt_add_of_neg_add_lt /-
protected theorem lt_add_of_neg_add_lt {a b c : ℤ} (h : -b + a < c) : a < b + c :=
  by
  have h := Int.add_lt_add_left h b
  rwa [Int.add_neg_cancel_left] at h 
#align int.lt_add_of_neg_add_lt Int.lt_add_of_neg_add_lt
-/

#print Int.neg_add_lt_of_lt_add /-
protected theorem neg_add_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : -b + a < c :=
  by
  have h := Int.add_lt_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h 
#align int.neg_add_lt_of_lt_add Int.neg_add_lt_of_lt_add
-/

#print Int.lt_add_of_sub_left_lt /-
protected theorem lt_add_of_sub_left_lt {a b c : ℤ} (h : a - b < c) : a < b + c :=
  by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h 
#align int.lt_add_of_sub_left_lt Int.lt_add_of_sub_left_lt
-/

#print Int.sub_left_lt_of_lt_add /-
protected theorem sub_left_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : a - b < c :=
  by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h 
#align int.sub_left_lt_of_lt_add Int.sub_left_lt_of_lt_add
-/

#print Int.lt_add_of_sub_right_lt /-
protected theorem lt_add_of_sub_right_lt {a b c : ℤ} (h : a - c < b) : a < b + c :=
  by
  have h := Int.add_lt_add_right h c
  rwa [Int.sub_add_cancel] at h 
#align int.lt_add_of_sub_right_lt Int.lt_add_of_sub_right_lt
-/

#print Int.sub_right_lt_of_lt_add /-
protected theorem sub_right_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : a - c < b :=
  by
  have h := Int.add_lt_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h 
#align int.sub_right_lt_of_lt_add Int.sub_right_lt_of_lt_add
-/

#print Int.lt_add_of_neg_add_lt_left /-
protected theorem lt_add_of_neg_add_lt_left {a b c : ℤ} (h : -b + a < c) : a < b + c :=
  by
  rw [Int.add_comm] at h 
  exact Int.lt_add_of_sub_left_lt h
#align int.lt_add_of_neg_add_lt_left Int.lt_add_of_neg_add_lt_left
-/

#print Int.neg_add_lt_left_of_lt_add /-
protected theorem neg_add_lt_left_of_lt_add {a b c : ℤ} (h : a < b + c) : -b + a < c :=
  by
  rw [Int.add_comm]
  exact Int.sub_left_lt_of_lt_add h
#align int.neg_add_lt_left_of_lt_add Int.neg_add_lt_left_of_lt_add
-/

#print Int.lt_add_of_neg_add_lt_right /-
protected theorem lt_add_of_neg_add_lt_right {a b c : ℤ} (h : -c + a < b) : a < b + c :=
  by
  rw [Int.add_comm] at h 
  exact Int.lt_add_of_sub_right_lt h
#align int.lt_add_of_neg_add_lt_right Int.lt_add_of_neg_add_lt_right
-/

#print Int.neg_add_lt_right_of_lt_add /-
protected theorem neg_add_lt_right_of_lt_add {a b c : ℤ} (h : a < b + c) : -c + a < b :=
  by
  rw [Int.add_comm] at h 
  exact Int.neg_add_lt_left_of_lt_add h
#align int.neg_add_lt_right_of_lt_add Int.neg_add_lt_right_of_lt_add
-/

#print Int.lt_add_of_neg_lt_sub_left /-
protected theorem lt_add_of_neg_lt_sub_left {a b c : ℤ} (h : -a < b - c) : c < a + b :=
  Int.lt_add_of_neg_add_lt_left (Int.add_lt_of_lt_sub_right h)
#align int.lt_add_of_neg_lt_sub_left Int.lt_add_of_neg_lt_sub_left
-/

#print Int.neg_lt_sub_left_of_lt_add /-
protected theorem neg_lt_sub_left_of_lt_add {a b c : ℤ} (h : c < a + b) : -a < b - c :=
  by
  have h := Int.lt_neg_add_of_add_lt (Int.sub_left_lt_of_lt_add h)
  rwa [Int.add_comm] at h 
#align int.neg_lt_sub_left_of_lt_add Int.neg_lt_sub_left_of_lt_add
-/

#print Int.lt_add_of_neg_lt_sub_right /-
protected theorem lt_add_of_neg_lt_sub_right {a b c : ℤ} (h : -b < a - c) : c < a + b :=
  Int.lt_add_of_sub_right_lt (Int.add_lt_of_lt_sub_left h)
#align int.lt_add_of_neg_lt_sub_right Int.lt_add_of_neg_lt_sub_right
-/

#print Int.neg_lt_sub_right_of_lt_add /-
protected theorem neg_lt_sub_right_of_lt_add {a b c : ℤ} (h : c < a + b) : -b < a - c :=
  Int.lt_sub_left_of_add_lt (Int.sub_right_lt_of_lt_add h)
#align int.neg_lt_sub_right_of_lt_add Int.neg_lt_sub_right_of_lt_add
-/

#print Int.sub_lt_of_sub_lt /-
protected theorem sub_lt_of_sub_lt {a b c : ℤ} (h : a - b < c) : a - c < b :=
  Int.sub_left_lt_of_lt_add (Int.lt_add_of_sub_right_lt h)
#align int.sub_lt_of_sub_lt Int.sub_lt_of_sub_lt
-/

#print Int.sub_lt_sub_left /-
protected theorem sub_lt_sub_left {a b : ℤ} (h : a < b) (c : ℤ) : c - b < c - a :=
  Int.add_lt_add_left (Int.neg_lt_neg h) c
#align int.sub_lt_sub_left Int.sub_lt_sub_left
-/

#print Int.sub_lt_sub_right /-
protected theorem sub_lt_sub_right {a b : ℤ} (h : a < b) (c : ℤ) : a - c < b - c :=
  Int.add_lt_add_right h (-c)
#align int.sub_lt_sub_right Int.sub_lt_sub_right
-/

#print Int.sub_lt_sub /-
protected theorem sub_lt_sub {a b c d : ℤ} (hab : a < b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_add hab (Int.neg_lt_neg hcd)
#align int.sub_lt_sub Int.sub_lt_sub
-/

#print Int.sub_lt_sub_of_le_of_lt /-
protected theorem sub_lt_sub_of_le_of_lt {a b c d : ℤ} (hab : a ≤ b) (hcd : c < d) :
    a - d < b - c :=
  Int.add_lt_add_of_le_of_lt hab (Int.neg_lt_neg hcd)
#align int.sub_lt_sub_of_le_of_lt Int.sub_lt_sub_of_le_of_lt
-/

#print Int.sub_lt_sub_of_lt_of_le /-
protected theorem sub_lt_sub_of_lt_of_le {a b c d : ℤ} (hab : a < b) (hcd : c ≤ d) :
    a - d < b - c :=
  Int.add_lt_add_of_lt_of_le hab (Int.neg_le_neg hcd)
#align int.sub_lt_sub_of_lt_of_le Int.sub_lt_sub_of_lt_of_le
-/

#print Int.sub_le_self /-
protected theorem sub_le_self (a : ℤ) {b : ℤ} (h : 0 ≤ b) : a - b ≤ a :=
  calc
    a - b = a + -b := rfl
    _ ≤ a + 0 := (Int.add_le_add_left (Int.neg_nonpos_of_nonneg h) _)
    _ = a := by rw [Int.add_zero]
#align int.sub_le_self Int.sub_le_self
-/

#print Int.sub_lt_self /-
protected theorem sub_lt_self (a : ℤ) {b : ℤ} (h : 0 < b) : a - b < a :=
  calc
    a - b = a + -b := rfl
    _ < a + 0 := (Int.add_lt_add_left (Int.neg_neg_of_pos h) _)
    _ = a := by rw [Int.add_zero]
#align int.sub_lt_self Int.sub_lt_self
-/

#print Int.add_le_add_three /-
protected theorem add_le_add_three {a b c d e f : ℤ} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
    a + b + c ≤ d + e + f := by
  apply le_trans
  apply Int.add_le_add
  apply Int.add_le_add
  assumption'
  apply le_refl
#align int.add_le_add_three Int.add_le_add_three
-/

end

/-! missing facts -/


#print Int.mul_lt_mul_of_pos_left /-
protected theorem mul_lt_mul_of_pos_left {a b c : ℤ} (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
  by
  have : 0 < b - a := Int.sub_pos_of_lt h₁
  have : 0 < c * (b - a) := Int.mul_pos h₂ this
  rw [Int.mul_sub] at this 
  exact Int.lt_of_sub_pos this
#align int.mul_lt_mul_of_pos_left Int.mul_lt_mul_of_pos_left
-/

#print Int.mul_lt_mul_of_pos_right /-
protected theorem mul_lt_mul_of_pos_right {a b c : ℤ} (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
  by
  have : 0 < b - a := Int.sub_pos_of_lt h₁
  have : 0 < (b - a) * c := Int.mul_pos this h₂
  rw [Int.sub_mul] at this 
  exact Int.lt_of_sub_pos this
#align int.mul_lt_mul_of_pos_right Int.mul_lt_mul_of_pos_right
-/

#print Int.mul_le_mul_of_nonneg_left /-
protected theorem mul_le_mul_of_nonneg_left {a b c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
  by
  by_cases hba : b ≤ a; · simp [le_antisymm hba h₁]
  by_cases hc0 : c ≤ 0; · simp [le_antisymm hc0 h₂, Int.zero_mul]
  exact
    (le_not_le_of_lt
        (Int.mul_lt_mul_of_pos_left (lt_of_le_not_le h₁ hba) (lt_of_le_not_le h₂ hc0))).left
#align int.mul_le_mul_of_nonneg_left Int.mul_le_mul_of_nonneg_left
-/

#print Int.mul_le_mul_of_nonneg_right /-
protected theorem mul_le_mul_of_nonneg_right {a b c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) :
    a * c ≤ b * c := by
  by_cases hba : b ≤ a; · simp [le_antisymm hba h₁]
  by_cases hc0 : c ≤ 0; · simp [le_antisymm hc0 h₂, Int.mul_zero]
  exact
    (le_not_le_of_lt
        (Int.mul_lt_mul_of_pos_right (lt_of_le_not_le h₁ hba) (lt_of_le_not_le h₂ hc0))).left
#align int.mul_le_mul_of_nonneg_right Int.mul_le_mul_of_nonneg_right
-/

#print Int.mul_le_mul /-
-- TODO: there are four variations, depending on which variables we assume to be nonneg
protected theorem mul_le_mul {a b c d : ℤ} (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b)
    (nn_c : 0 ≤ c) : a * b ≤ c * d :=
  calc
    a * b ≤ c * b := Int.mul_le_mul_of_nonneg_right hac nn_b
    _ ≤ c * d := Int.mul_le_mul_of_nonneg_left hbd nn_c
#align int.mul_le_mul Int.mul_le_mul
-/

#print Int.mul_nonpos_of_nonneg_of_nonpos /-
protected theorem mul_nonpos_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 :=
  by
  have h : a * b ≤ a * 0 := Int.mul_le_mul_of_nonneg_left hb ha
  rwa [Int.mul_zero] at h 
#align int.mul_nonpos_of_nonneg_of_nonpos Int.mul_nonpos_of_nonneg_of_nonpos
-/

#print Int.mul_nonpos_of_nonpos_of_nonneg /-
protected theorem mul_nonpos_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 :=
  by
  have h : a * b ≤ 0 * b := Int.mul_le_mul_of_nonneg_right ha hb
  rwa [Int.zero_mul] at h 
#align int.mul_nonpos_of_nonpos_of_nonneg Int.mul_nonpos_of_nonpos_of_nonneg
-/

#print Int.mul_lt_mul /-
protected theorem mul_lt_mul {a b c d : ℤ} (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b)
    (nn_c : 0 ≤ c) : a * b < c * d :=
  calc
    a * b < c * b := Int.mul_lt_mul_of_pos_right hac pos_b
    _ ≤ c * d := Int.mul_le_mul_of_nonneg_left hbd nn_c
#align int.mul_lt_mul Int.mul_lt_mul
-/

#print Int.mul_lt_mul' /-
protected theorem mul_lt_mul' {a b c d : ℤ} (h1 : a ≤ c) (h2 : b < d) (h3 : 0 ≤ b) (h4 : 0 < c) :
    a * b < c * d :=
  calc
    a * b ≤ c * b := Int.mul_le_mul_of_nonneg_right h1 h3
    _ < c * d := Int.mul_lt_mul_of_pos_left h2 h4
#align int.mul_lt_mul' Int.mul_lt_mul'
-/

#print Int.mul_neg_of_pos_of_neg /-
protected theorem mul_neg_of_pos_of_neg {a b : ℤ} (ha : 0 < a) (hb : b < 0) : a * b < 0 :=
  by
  have h : a * b < a * 0 := Int.mul_lt_mul_of_pos_left hb ha
  rwa [Int.mul_zero] at h 
#align int.mul_neg_of_pos_of_neg Int.mul_neg_of_pos_of_neg
-/

#print Int.mul_neg_of_neg_of_pos /-
protected theorem mul_neg_of_neg_of_pos {a b : ℤ} (ha : a < 0) (hb : 0 < b) : a * b < 0 :=
  by
  have h : a * b < 0 * b := Int.mul_lt_mul_of_pos_right ha hb
  rwa [Int.zero_mul] at h 
#align int.mul_neg_of_neg_of_pos Int.mul_neg_of_neg_of_pos
-/

#print Int.mul_le_mul_of_nonpos_right /-
protected theorem mul_le_mul_of_nonpos_right {a b c : ℤ} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
  have : -c ≥ 0 := Int.neg_nonneg_of_nonpos hc
  have : b * -c ≤ a * -c := Int.mul_le_mul_of_nonneg_right h this
  have : -(b * c) ≤ -(a * c) := by rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this 
  Int.le_of_neg_le_neg this
#align int.mul_le_mul_of_nonpos_right Int.mul_le_mul_of_nonpos_right
-/

#print Int.mul_nonneg_of_nonpos_of_nonpos /-
protected theorem mul_nonneg_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b :=
  by
  have : 0 * b ≤ a * b := Int.mul_le_mul_of_nonpos_right ha hb
  rwa [Int.zero_mul] at this 
#align int.mul_nonneg_of_nonpos_of_nonpos Int.mul_nonneg_of_nonpos_of_nonpos
-/

#print Int.mul_lt_mul_of_neg_left /-
protected theorem mul_lt_mul_of_neg_left {a b c : ℤ} (h : b < a) (hc : c < 0) : c * a < c * b :=
  have : -c > 0 := Int.neg_pos_of_neg hc
  have : -c * b < -c * a := Int.mul_lt_mul_of_pos_left h this
  have : -(c * b) < -(c * a) := by rwa [← Int.neg_mul_eq_neg_mul, ← Int.neg_mul_eq_neg_mul] at this 
  Int.lt_of_neg_lt_neg this
#align int.mul_lt_mul_of_neg_left Int.mul_lt_mul_of_neg_left
-/

#print Int.mul_lt_mul_of_neg_right /-
protected theorem mul_lt_mul_of_neg_right {a b c : ℤ} (h : b < a) (hc : c < 0) : a * c < b * c :=
  have : -c > 0 := Int.neg_pos_of_neg hc
  have : b * -c < a * -c := Int.mul_lt_mul_of_pos_right h this
  have : -(b * c) < -(a * c) := by rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this 
  Int.lt_of_neg_lt_neg this
#align int.mul_lt_mul_of_neg_right Int.mul_lt_mul_of_neg_right
-/

#print Int.mul_pos_of_neg_of_neg /-
protected theorem mul_pos_of_neg_of_neg {a b : ℤ} (ha : a < 0) (hb : b < 0) : 0 < a * b :=
  by
  have : 0 * b < a * b := Int.mul_lt_mul_of_neg_right ha hb
  rwa [Int.zero_mul] at this 
#align int.mul_pos_of_neg_of_neg Int.mul_pos_of_neg_of_neg
-/

#print Int.mul_self_le_mul_self /-
protected theorem mul_self_le_mul_self {a b : ℤ} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
  Int.mul_le_mul h2 h2 h1 (le_trans h1 h2)
#align int.mul_self_le_mul_self Int.mul_self_le_mul_self
-/

#print Int.mul_self_lt_mul_self /-
protected theorem mul_self_lt_mul_self {a b : ℤ} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  Int.mul_lt_mul' (le_of_lt h2) h2 h1 (lt_of_le_of_lt h1 h2)
#align int.mul_self_lt_mul_self Int.mul_self_lt_mul_self
-/

/-! more facts specific to int -/


#print Int.ofNat_nonneg /-
theorem ofNat_nonneg (n : ℕ) : 0 ≤ ofNat n :=
  trivial
#align int.of_nat_nonneg Int.ofNat_nonneg
-/

#print Int.ofNat_succ_pos /-
theorem ofNat_succ_pos (n : Nat) : 0 < (Nat.succ n : ℤ) :=
  ofNat_lt_ofNat_of_lt (Nat.succ_pos _)
#align int.coe_succ_pos Int.ofNat_succ_pos
-/

#print Int.exists_eq_neg_ofNat /-
theorem exists_eq_neg_ofNat {a : ℤ} (H : a ≤ 0) : ∃ n : ℕ, a = -n :=
  let ⟨n, h⟩ := eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos H)
  ⟨n, Int.eq_neg_of_eq_neg h.symm⟩
#align int.exists_eq_neg_of_nat Int.exists_eq_neg_ofNat
-/

#print Int.natAbs_of_nonneg /-
theorem natAbs_of_nonneg {a : ℤ} (H : 0 ≤ a) : (natAbs a : ℤ) = a :=
  match a, eq_ofNat_of_zero_le H with
  | _, ⟨n, rfl⟩ => rfl
#align int.nat_abs_of_nonneg Int.natAbs_of_nonneg
-/

#print Int.ofNat_natAbs_of_nonpos /-
theorem ofNat_natAbs_of_nonpos {a : ℤ} (H : a ≤ 0) : (natAbs a : ℤ) = -a := by
  rw [← nat_abs_neg, nat_abs_of_nonneg (Int.neg_nonneg_of_nonpos H)]
#align int.of_nat_nat_abs_of_nonpos Int.ofNat_natAbs_of_nonpos
-/

#print Int.lt_of_add_one_le /-
theorem lt_of_add_one_le {a b : ℤ} (H : a + 1 ≤ b) : a < b :=
  H
#align int.lt_of_add_one_le Int.lt_of_add_one_le
-/

#print Int.add_one_le_of_lt /-
theorem add_one_le_of_lt {a b : ℤ} (H : a < b) : a + 1 ≤ b :=
  H
#align int.add_one_le_of_lt Int.add_one_le_of_lt
-/

#print Int.lt_add_one_of_le /-
theorem lt_add_one_of_le {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
  Int.add_le_add_right H 1
#align int.lt_add_one_of_le Int.lt_add_one_of_le
-/

#print Int.le_of_lt_add_one /-
theorem le_of_lt_add_one {a b : ℤ} (H : a < b + 1) : a ≤ b :=
  Int.le_of_add_le_add_right H
#align int.le_of_lt_add_one Int.le_of_lt_add_one
-/

#print Int.sub_one_lt_of_le /-
theorem sub_one_lt_of_le {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
  Int.sub_right_lt_of_lt_add <| lt_add_one_of_le H
#align int.sub_one_lt_of_le Int.sub_one_lt_of_le
-/

#print Int.le_of_sub_one_lt /-
theorem le_of_sub_one_lt {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
  le_of_lt_add_one <| Int.lt_add_of_sub_right_lt H
#align int.le_of_sub_one_lt Int.le_of_sub_one_lt
-/

#print Int.le_sub_one_of_lt /-
theorem le_sub_one_of_lt {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
  Int.le_sub_right_of_add_le H
#align int.le_sub_one_of_lt Int.le_sub_one_of_lt
-/

#print Int.lt_of_le_sub_one /-
theorem lt_of_le_sub_one {a b : ℤ} (H : a ≤ b - 1) : a < b :=
  Int.add_le_of_le_sub_right H
#align int.lt_of_le_sub_one Int.lt_of_le_sub_one
-/

#print Int.sign_of_succ /-
theorem sign_of_succ (n : Nat) : sign (Nat.succ n) = 1 :=
  rfl
#align int.sign_of_succ Int.sign_of_succ
-/

#print Int.sign_eq_one_of_pos /-
theorem sign_eq_one_of_pos {a : ℤ} (h : 0 < a) : sign a = 1 :=
  match a, eq_succ_of_zero_lt h with
  | _, ⟨n, rfl⟩ => rfl
#align int.sign_eq_one_of_pos Int.sign_eq_one_of_pos
-/

#print Int.sign_eq_neg_one_of_neg /-
theorem sign_eq_neg_one_of_neg {a : ℤ} (h : a < 0) : sign a = -1 :=
  match a, eq_negSucc_of_lt_zero h with
  | _, ⟨n, rfl⟩ => rfl
#align int.sign_eq_neg_one_of_neg Int.sign_eq_neg_one_of_neg
-/

#print Int.eq_zero_of_sign_eq_zero /-
theorem eq_zero_of_sign_eq_zero : ∀ {a : ℤ}, sign a = 0 → a = 0
  | 0, _ => rfl
#align int.eq_zero_of_sign_eq_zero Int.eq_zero_of_sign_eq_zero
-/

#print Int.pos_of_sign_eq_one /-
theorem pos_of_sign_eq_one : ∀ {a : ℤ}, sign a = 1 → 0 < a
  | (n + 1 : ℕ), _ => ofNat_lt_ofNat_of_lt (Nat.succ_pos _)
#align int.pos_of_sign_eq_one Int.pos_of_sign_eq_one
-/

#print Int.neg_of_sign_eq_neg_one /-
theorem neg_of_sign_eq_neg_one : ∀ {a : ℤ}, sign a = -1 → a < 0
  | (n + 1 : ℕ), h => nomatch h
  | 0, h => nomatch h
  | -[n+1], _ => negSucc_lt_zero _
#align int.neg_of_sign_eq_neg_one Int.neg_of_sign_eq_neg_one
-/

#print Int.sign_eq_one_iff_pos /-
theorem sign_eq_one_iff_pos (a : ℤ) : sign a = 1 ↔ 0 < a :=
  ⟨pos_of_sign_eq_one, sign_eq_one_of_pos⟩
#align int.sign_eq_one_iff_pos Int.sign_eq_one_iff_pos
-/

#print Int.sign_eq_neg_one_iff_neg /-
theorem sign_eq_neg_one_iff_neg (a : ℤ) : sign a = -1 ↔ a < 0 :=
  ⟨neg_of_sign_eq_neg_one, sign_eq_neg_one_of_neg⟩
#align int.sign_eq_neg_one_iff_neg Int.sign_eq_neg_one_iff_neg
-/

#print Int.sign_eq_zero_iff_zero /-
theorem sign_eq_zero_iff_zero (a : ℤ) : sign a = 0 ↔ a = 0 :=
  ⟨eq_zero_of_sign_eq_zero, fun h => by rw [h, sign_zero]⟩
#align int.sign_eq_zero_iff_zero Int.sign_eq_zero_iff_zero
-/

#print Int.eq_zero_or_eq_zero_of_mul_eq_zero /-
protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  match lt_trichotomy 0 a with
  | Or.inl hlt₁ =>
    match lt_trichotomy 0 b with
    | Or.inl hlt₂ => by
      have : 0 < a * b := Int.mul_pos hlt₁ hlt₂
      rw [h] at this 
      exact absurd this (lt_irrefl _)
    | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
    | Or.inr (Or.inr hgt₂) =>
      by
      have : 0 > a * b := Int.mul_neg_of_pos_of_neg hlt₁ hgt₂
      rw [h] at this 
      exact absurd this (lt_irrefl _)
  | Or.inr (Or.inl heq₁) => Or.inl heq₁.symm
  | Or.inr (Or.inr hgt₁) =>
    match lt_trichotomy 0 b with
    | Or.inl hlt₂ => by
      have : 0 > a * b := Int.mul_neg_of_neg_of_pos hgt₁ hlt₂
      rw [h] at this 
      exact absurd this (lt_irrefl _)
    | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
    | Or.inr (Or.inr hgt₂) =>
      by
      have : 0 < a * b := Int.mul_pos_of_neg_of_neg hgt₁ hgt₂
      rw [h] at this 
      exact absurd this (lt_irrefl _)
#align int.eq_zero_or_eq_zero_of_mul_eq_zero Int.eq_zero_or_eq_zero_of_mul_eq_zero
-/

#print Int.eq_of_mul_eq_mul_right /-
protected theorem eq_of_mul_eq_mul_right {a b c : ℤ} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have : b * a - c * a = 0 := Int.sub_eq_zero_of_eq h
  have : (b - c) * a = 0 := by rw [Int.sub_mul, this]
  have : b - c = 0 := (Int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha
  Int.eq_of_sub_eq_zero this
#align int.eq_of_mul_eq_mul_right Int.eq_of_mul_eq_mul_right
-/

#print Int.eq_of_mul_eq_mul_left /-
protected theorem eq_of_mul_eq_mul_left {a b c : ℤ} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have : a * b - a * c = 0 := Int.sub_eq_zero_of_eq h
  have : a * (b - c) = 0 := by rw [Int.mul_sub, this]
  have : b - c = 0 := (Int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha
  Int.eq_of_sub_eq_zero this
#align int.eq_of_mul_eq_mul_left Int.eq_of_mul_eq_mul_left
-/

#print Int.eq_one_of_mul_eq_self_left /-
theorem eq_one_of_mul_eq_self_left {a b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
  Int.eq_of_mul_eq_mul_right Hpos (by rw [Int.one_mul, H])
#align int.eq_one_of_mul_eq_self_left Int.eq_one_of_mul_eq_self_left
-/

#print Int.eq_one_of_mul_eq_self_right /-
theorem eq_one_of_mul_eq_self_right {a b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
  Int.eq_of_mul_eq_mul_left Hpos (by rw [Int.mul_one, H])
#align int.eq_one_of_mul_eq_self_right Int.eq_one_of_mul_eq_self_right
-/

end Int

