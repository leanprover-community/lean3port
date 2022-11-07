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

#print Int /-
-- the type, coercions, and notation
inductive Int : Type
  | of_nat : Nat → Int
  | neg_succ_of_nat : Nat → Int
  deriving DecidableEq
-/

instance : Coe Nat Int :=
  ⟨Int.ofNat⟩

#print Int.repr /-
protected def Int.repr : Int → String
  | Int.ofNat n => repr n
  | Int.negSucc n => "-" ++ repr (succ n)
-/

instance : Repr Int :=
  ⟨Int.repr⟩

instance : ToString Int :=
  ⟨Int.repr⟩

namespace Int

protected theorem coe_nat_eq (n : ℕ) : ↑n = Int.ofNat n :=
  rfl

protected def zero : ℤ :=
  ofNat 0

protected def one : ℤ :=
  ofNat 1

instance : Zero ℤ :=
  ⟨Int.zero⟩

instance : One ℤ :=
  ⟨Int.one⟩

theorem of_nat_zero : ofNat (0 : Nat) = (0 : Int) :=
  rfl

theorem of_nat_one : ofNat (1 : Nat) = (1 : Int) :=
  rfl

#print Int.negOfNat /-
-- definitions of basic functions
def negOfNat : ℕ → ℤ
  | 0 => 0
  | succ m => -[m+1]
-/

#print Int.subNatNat /-
def subNatNat (m n : ℕ) : ℤ :=
  match (n - m : Nat) with
  | 0 => ofNat (m - n)
  |-- m ≥ n
      succ
      k =>
    -[k+1]
-/

-- m < n, and n - m = succ k
theorem sub_nat_nat_of_sub_eq_zero {m n : ℕ} (h : n - m = 0) : subNatNat m n = ofNat (m - n) := by
  unfold sub_nat_nat
  rw [h]
  unfold sub_nat_nat._match_1

theorem sub_nat_nat_of_sub_eq_succ {m n k : ℕ} (h : n - m = succ k) : subNatNat m n = -[k+1] := by
  unfold sub_nat_nat
  rw [h]
  unfold sub_nat_nat._match_1

#print Int.neg /-
protected def neg : ℤ → ℤ
  | of_nat n => negOfNat n
  | -[n+1] => succ n
-/

#print Int.add /-
protected def add : ℤ → ℤ → ℤ
  | of_nat m, of_nat n => ofNat (m + n)
  | of_nat m, -[n+1] => subNatNat m (succ n)
  | -[m+1], of_nat n => subNatNat n (succ m)
  | -[m+1], -[n+1] => -[succ (m + n)+1]
-/

#print Int.mul /-
protected def mul : ℤ → ℤ → ℤ
  | of_nat m, of_nat n => ofNat (m * n)
  | of_nat m, -[n+1] => negOfNat (m * succ n)
  | -[m+1], of_nat n => negOfNat (succ m * n)
  | -[m+1], -[n+1] => ofNat (succ m * succ n)
-/

instance : Neg ℤ :=
  ⟨Int.neg⟩

instance : Add ℤ :=
  ⟨Int.add⟩

instance : Mul ℤ :=
  ⟨Int.mul⟩

#print Int.sub /-
-- defeq to algebra.sub which gives subtraction for arbitrary `add_group`s
protected def sub : ℤ → ℤ → ℤ := fun m n => m + -n
-/

instance : Sub ℤ :=
  ⟨Int.sub⟩

#print Int.neg_zero /-
protected theorem neg_zero : -(0 : ℤ) = 0 :=
  rfl
-/

theorem of_nat_add (n m : ℕ) : ofNat (n + m) = ofNat n + ofNat m :=
  rfl

theorem of_nat_mul (n m : ℕ) : ofNat (n * m) = ofNat n * ofNat m :=
  rfl

theorem of_nat_succ (n : ℕ) : ofNat (succ n) = ofNat n + 1 :=
  rfl

theorem neg_of_nat_zero : -ofNat 0 = 0 :=
  rfl

theorem neg_of_nat_of_succ (n : ℕ) : -ofNat (succ n) = -[n+1] :=
  rfl

theorem neg_neg_of_nat_succ (n : ℕ) : - -[n+1] = ofNat (succ n) :=
  rfl

theorem of_nat_eq_coe (n : ℕ) : ofNat n = ↑n :=
  rfl

theorem neg_succ_of_nat_coe (n : ℕ) : -[n+1] = -↑(n + 1) :=
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

theorem of_nat_add_neg_succ_of_nat (m n : Nat) : ofNat m + -[n+1] = subNatNat m (succ n) :=
  rfl

theorem neg_succ_of_nat_add_of_nat (m n : Nat) : -[m+1] + ofNat n = subNatNat n (succ m) :=
  rfl

theorem neg_succ_of_nat_add_neg_succ_of_nat (m n : Nat) : -[m+1] + -[n+1] = -[succ (m + n)+1] :=
  rfl

theorem of_nat_mul_of_nat (m n : Nat) : ofNat m * ofNat n = ofNat (m * n) :=
  rfl

theorem of_nat_mul_neg_succ_of_nat (m n : Nat) : ofNat m * -[n+1] = negOfNat (m * succ n) :=
  rfl

theorem neg_succ_of_nat_of_nat (m n : Nat) : -[m+1] * ofNat n = negOfNat (succ m * n) :=
  rfl

theorem mul_neg_succ_of_nat_neg_succ_of_nat (m n : Nat) : -[m+1] * -[n+1] = ofNat (succ m * succ n) :=
  rfl

attribute [local simp]
  of_nat_add_of_nat of_nat_mul_of_nat neg_of_nat_zero neg_of_nat_of_succ neg_neg_of_nat_succ of_nat_add_neg_succ_of_nat neg_succ_of_nat_add_of_nat neg_succ_of_nat_add_neg_succ_of_nat of_nat_mul_neg_succ_of_nat neg_succ_of_nat_of_nat mul_neg_succ_of_nat_neg_succ_of_nat

#print Int.coe_nat_inj /-
-- some basic functions and properties
protected theorem coe_nat_inj {m n : ℕ} (h : (↑m : ℤ) = ↑n) : m = n :=
  Int.ofNat.inj h
-/

theorem of_nat_eq_of_nat_iff (m n : ℕ) : ofNat m = ofNat n ↔ m = n :=
  Iff.intro Int.ofNat.inj (congr_arg _)

protected theorem coe_nat_eq_coe_nat_iff (m n : ℕ) : (↑m : ℤ) = ↑n ↔ m = n :=
  of_nat_eq_of_nat_iff m n

theorem neg_succ_of_nat_inj_iff {m n : ℕ} : negSucc m = negSucc n ↔ m = n :=
  ⟨negSucc.inj, fun H => by simp [H]⟩

theorem neg_succ_of_nat_eq (n : ℕ) : -[n+1] = -(n + 1) :=
  rfl

#print Int.neg_neg /-
-- neg
protected theorem neg_neg : ∀ a : ℤ, - -a = a
  | of_nat 0 => rfl
  | of_nat (n + 1) => rfl
  | -[n+1] => rfl
-/

/- warning: int.neg_inj -> Int.neg_inj is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (Eq.{1} Int (Neg.neg.{0} Int Int.hasNeg a) (Neg.neg.{0} Int Int.hasNeg b)) -> (Eq.{1} Int a b)
but is expected to have type
  forall {a : Int} {b : Int}, Iff (Eq.{1} Int (Neg.neg.{0} Int Int.instNegInt a) (Neg.neg.{0} Int Int.instNegInt b)) (Eq.{1} Int a b)
Case conversion may be inaccurate. Consider using '#align int.neg_inj Int.neg_injₓ'. -/
protected theorem neg_inj {a b : ℤ} (h : -a = -b) : a = b := by rw [← Int.neg_neg a, ← Int.neg_neg b, h]

#print Int.sub_eq_add_neg /-
protected theorem sub_eq_add_neg {a b : ℤ} : a - b = a + -b :=
  rfl
-/

-- basic properties of sub_nat_nat
theorem sub_nat_nat_elim (m n : ℕ) (P : ℕ → ℕ → ℤ → Prop) (hp : ∀ i n, P (n + i) n (ofNat i))
    (hn : ∀ i m, P m (m + i + 1) -[i+1]) : P m n (subNatNat m n) := by
  have H : ∀ k, n - m = k → P m n (Nat.casesOn k (of_nat (m - n)) fun a => -[a+1]) := by
    intro k
    cases k
    · intro e
      cases' Nat.le.dest (Nat.le_of_sub_eq_zero e) with k h
      rw [h.symm, Nat.add_sub_cancel_left]
      apply hp
      
    · intro heq
      have h : m ≤ n := Nat.le_of_lt (Nat.lt_of_sub_eq_succ HEq)
      rw [Nat.sub_eq_iff_eq_add h] at heq
      rw [HEq, Nat.add_comm]
      apply hn
      
  delta sub_nat_nat
  exact H _ rfl

theorem sub_nat_nat_add_left {m n : ℕ} : subNatNat (m + n) m = ofNat n := by
  dsimp only [sub_nat_nat]
  rw [Nat.sub_eq_zero_of_le]
  dsimp only [sub_nat_nat._match_1]
  rw [Nat.add_sub_cancel_left]
  apply Nat.le_add_right

theorem sub_nat_nat_add_right {m n : ℕ} : subNatNat m (m + n + 1) = negSucc n :=
  calc
    SubNatNat._match1 m (m + n + 1) (m + n + 1 - m) = SubNatNat._match1 m (m + n + 1) (m + (n + 1) - m) := by
      rw [Nat.add_assoc]
    _ = SubNatNat._match1 m (m + n + 1) (n + 1) := by rw [Nat.add_sub_cancel_left]
    _ = negSucc n := rfl
    

theorem sub_nat_nat_add_add (m n k : ℕ) : subNatNat (m + k) (n + k) = subNatNat m n :=
  sub_nat_nat_elim m n (fun m n i => subNatNat (m + k) (n + k) = i)
    (fun i n => by
      have : n + i + k = n + k + i := by simp [Nat.add_comm, Nat.add_left_comm]
      rw [this]
      exact sub_nat_nat_add_left)
    fun i m => by
    have : m + i + 1 + k = m + k + i + 1 := by simp [Nat.add_comm, Nat.add_left_comm]
    rw [this]
    exact sub_nat_nat_add_right

theorem sub_nat_nat_of_le {m n : ℕ} (h : n ≤ m) : subNatNat m n = ofNat (m - n) :=
  sub_nat_nat_of_sub_eq_zero (Nat.sub_eq_zero_of_le h)

theorem sub_nat_nat_of_lt {m n : ℕ} (h : m < n) : subNatNat m n = -[pred (n - m)+1] := by
  have : n - m = succ (pred (n - m)) := Eq.symm (succ_pred_eq_of_pos (Nat.sub_pos_of_lt h))
  rw [sub_nat_nat_of_sub_eq_succ this]

#print Int.natAbs /-
-- nat_abs
@[simp]
def natAbs : ℤ → ℕ
  | of_nat m => m
  | -[m+1] => succ m
-/

theorem nat_abs_of_nat (n : ℕ) : natAbs ↑n = n :=
  rfl

theorem eq_zero_of_nat_abs_eq_zero : ∀ {a : ℤ}, natAbs a = 0 → a = 0
  | of_nat m, H => congr_arg ofNat H
  | -[m'+1], H => absurd H (succ_ne_zero _)

theorem nat_abs_pos_of_ne_zero {a : ℤ} (h : a ≠ 0) : 0 < natAbs a :=
  (Nat.eq_zero_or_pos _).resolve_left <| mt eq_zero_of_nat_abs_eq_zero h

theorem nat_abs_zero : natAbs (0 : Int) = (0 : Nat) :=
  rfl

theorem nat_abs_one : natAbs (1 : Int) = (1 : Nat) :=
  rfl

theorem nat_abs_mul_self : ∀ {a : ℤ}, ↑(natAbs a * natAbs a) = a * a
  | of_nat m => rfl
  | -[m'+1] => rfl

@[simp]
theorem nat_abs_neg (a : ℤ) : natAbs (-a) = natAbs a := by
  cases' a with n n
  cases n <;> rfl
  rfl

theorem nat_abs_eq : ∀ a : ℤ, a = natAbs a ∨ a = -natAbs a
  | of_nat m => Or.inl rfl
  | -[m'+1] => Or.inr rfl

theorem eq_coe_or_neg (a : ℤ) : ∃ n : ℕ, a = n ∨ a = -n :=
  ⟨_, nat_abs_eq a⟩

#print Int.sign /-
-- sign
def sign : ℤ → ℤ
  | (n + 1 : ℕ) => 1
  | 0 => 0
  | -[n+1] => -1
-/

#print Int.sign_zero /-
@[simp]
theorem sign_zero : sign 0 = 0 :=
  rfl
-/

#print Int.sign_one /-
@[simp]
theorem sign_one : sign 1 = 1 :=
  rfl
-/

#print Int.sign_neg_one /-
@[simp]
theorem sign_neg_one : sign (-1) = -1 :=
  rfl
-/

#print Int.div /-
-- Quotient and remainder 
-- There are three main conventions for integer division,
-- referred here as the E, F, T rounding conventions.
-- All three pairs satisfy the identity x % y + (x / y) * y = x
-- unconditionally.
-- E-rounding: This pair satisfies 0 ≤ mod x y < nat_abs y for y ≠ 0
protected def div : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => ofNat (m / n)
  | (m : ℕ), -[n+1] => -ofNat (m / succ n)
  | -[m+1], 0 => 0
  | -[m+1], (n + 1 : ℕ) => -[m / succ n+1]
  | -[m+1], -[n+1] => ofNat (succ (m / succ n))
-/

#print Int.mod /-
protected def mod : ℤ → ℤ → ℤ
  | (m : ℕ), n => (m % natAbs n : ℕ)
  | -[m+1], n => subNatNat (natAbs n) (succ (m % natAbs n))
-/

#print Int.fdiv /-
-- F-rounding: This pair satisfies fdiv x y = floor (x / y)
def fdiv : ℤ → ℤ → ℤ
  | 0, _ => 0
  | (m : ℕ), (n : ℕ) => ofNat (m / n)
  | (m + 1 : ℕ), -[n+1] => -[m / succ n+1]
  | -[m+1], 0 => 0
  | -[m+1], (n + 1 : ℕ) => -[m / succ n+1]
  | -[m+1], -[n+1] => ofNat (succ m / succ n)
-/

#print Int.fmod /-
def fmod : ℤ → ℤ → ℤ
  | 0, _ => 0
  | (m : ℕ), (n : ℕ) => ofNat (m % n)
  | (m + 1 : ℕ), -[n+1] => subNatNat (m % succ n) n
  | -[m+1], (n : ℕ) => subNatNat n (succ (m % n))
  | -[m+1], -[n+1] => -ofNat (succ m % succ n)
-/

-- T-rounding: This pair satisfies quot x y = round_to_zero (x / y)
def quot : ℤ → ℤ → ℤ
  | of_nat m, of_nat n => ofNat (m / n)
  | of_nat m, -[n+1] => -ofNat (m / succ n)
  | -[m+1], of_nat n => -ofNat (succ m / n)
  | -[m+1], -[n+1] => ofNat (succ m / succ n)

def rem : ℤ → ℤ → ℤ
  | of_nat m, of_nat n => ofNat (m % n)
  | of_nat m, -[n+1] => ofNat (m % succ n)
  | -[m+1], of_nat n => -ofNat (succ m % n)
  | -[m+1], -[n+1] => -ofNat (succ m % succ n)

instance : Div ℤ :=
  ⟨Int.div⟩

instance : Mod ℤ :=
  ⟨Int.mod⟩

#print Int.gcd /-
-- gcd
def gcd (m n : ℤ) : ℕ :=
  gcd (natAbs m) (natAbs n)
-/

#print Int.add_comm /-
/-
   int is a ring
-/
-- addition
protected theorem add_comm : ∀ a b : ℤ, a + b = b + a
  | of_nat n, of_nat m => by simp [Nat.add_comm]
  | of_nat n, -[m+1] => rfl
  | -[n+1], of_nat m => rfl
  | -[n+1], -[m+1] => by simp [Nat.add_comm]
-/

#print Int.add_zero /-
protected theorem add_zero : ∀ a : ℤ, a + 0 = a
  | of_nat n => rfl
  | -[n+1] => rfl
-/

#print Int.zero_add /-
protected theorem zero_add (a : ℤ) : 0 + a = a :=
  Int.add_comm a 0 ▸ Int.add_zero a
-/

theorem sub_nat_nat_sub {m n : ℕ} (h : n ≤ m) (k : ℕ) : subNatNat (m - n) k = subNatNat m (k + n) :=
  calc
    subNatNat (m - n) k = subNatNat (m - n + n) (k + n) := by rw [sub_nat_nat_add_add]
    _ = subNatNat m (k + n) := by rw [Nat.sub_add_cancel h]
    

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:52:50: missing argument -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in transitivity #[[]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:55:35: expecting parse arg -/
theorem sub_nat_nat_add (m n k : ℕ) : subNatNat (m + n) k = ofNat m + subNatNat n k := by
  have h := le_or_lt k n
  cases' h with h' h'
  · rw [sub_nat_nat_of_le h']
    have h₂ : k ≤ m + n := le_trans h' (Nat.le_add_left _ _)
    rw [sub_nat_nat_of_le h₂]
    simp
    rw [Nat.add_sub_assoc h']
    
  rw [sub_nat_nat_of_lt h']
  simp
  rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in transitivity #[[]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:55:35: expecting parse arg"
  rw [← Nat.sub_add_cancel (le_of_lt h')]
  apply sub_nat_nat_add_add

theorem sub_nat_nat_add_neg_succ_of_nat (m n k : ℕ) : subNatNat m n + -[k+1] = subNatNat m (n + succ k) := by
  have h := le_or_lt n m
  cases' h with h' h'
  · rw [sub_nat_nat_of_le h']
    simp
    rw [sub_nat_nat_sub h', Nat.add_comm]
    
  have h₂ : m < n + succ k := Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _)
  have h₃ : m ≤ n + k := le_of_succ_le_succ h₂
  rw [sub_nat_nat_of_lt h', sub_nat_nat_of_lt h₂]
  simp [Nat.add_comm]
  rw [← add_succ, succ_pred_eq_of_pos (Nat.sub_pos_of_lt h'), add_succ, succ_sub h₃, pred_succ]
  rw [Nat.add_comm n, Nat.add_sub_assoc (le_of_lt h')]

theorem add_assoc_aux1 (m n : ℕ) : ∀ c : ℤ, ofNat m + ofNat n + c = ofNat m + (ofNat n + c)
  | of_nat k => by simp [Nat.add_assoc]
  | -[k+1] => by simp [sub_nat_nat_add]

theorem add_assoc_aux2 (m n k : ℕ) : -[m+1] + -[n+1] + ofNat k = -[m+1] + (-[n+1] + ofNat k) := by
  simp [add_succ]
  rw [Int.add_comm, sub_nat_nat_add_neg_succ_of_nat]
  simp [add_succ, succ_add, Nat.add_comm]

#print Int.add_assoc /-
protected theorem add_assoc : ∀ a b c : ℤ, a + b + c = a + (b + c)
  | of_nat m, of_nat n, c => add_assoc_aux1 _ _ _
  | of_nat m, b, of_nat k => by
    rw [Int.add_comm, ← add_assoc_aux1, Int.add_comm (of_nat k), add_assoc_aux1, Int.add_comm b]
  | a, of_nat n, of_nat k => by
    rw [Int.add_comm, Int.add_comm a, ← add_assoc_aux1, Int.add_comm a, Int.add_comm (of_nat k)]
  | -[m+1], -[n+1], of_nat k => add_assoc_aux2 _ _ _
  | -[m+1], of_nat n, -[k+1] => by
    rw [Int.add_comm, ← add_assoc_aux2, Int.add_comm (of_nat n), ← add_assoc_aux2, Int.add_comm -[m+1]]
  | of_nat m, -[n+1], -[k+1] => by
    rw [Int.add_comm, Int.add_comm (of_nat m), Int.add_comm (of_nat m), ← add_assoc_aux2, Int.add_comm -[k+1]]
  | -[m+1], -[n+1], -[k+1] => by simp [add_succ, Nat.add_comm, Nat.add_left_comm, neg_of_nat_of_succ]
-/

#print Int.sub_nat_self /-
-- negation
theorem sub_nat_self : ∀ n, subNatNat n n = 0
  | 0 => rfl
  | succ m => by
    rw [sub_nat_nat_of_sub_eq_zero, Nat.sub_self, of_nat_zero]
    rw [Nat.sub_self]
-/

attribute [local simp] sub_nat_self

#print Int.add_left_neg /-
protected theorem add_left_neg : ∀ a : ℤ, -a + a = 0
  | of_nat 0 => rfl
  | of_nat (succ m) => by simp
  | -[m+1] => by simp
-/

#print Int.add_right_neg /-
protected theorem add_right_neg (a : ℤ) : a + -a = 0 := by rw [Int.add_comm, Int.add_left_neg]
-/

#print Int.mul_comm /-
-- multiplication
protected theorem mul_comm : ∀ a b : ℤ, a * b = b * a
  | of_nat m, of_nat n => by simp [Nat.mul_comm]
  | of_nat m, -[n+1] => by simp [Nat.mul_comm]
  | -[m+1], of_nat n => by simp [Nat.mul_comm]
  | -[m+1], -[n+1] => by simp [Nat.mul_comm]
-/

theorem of_nat_mul_neg_of_nat (m : ℕ) : ∀ n, ofNat m * negOfNat n = negOfNat (m * n)
  | 0 => rfl
  | succ n => by
    unfold neg_of_nat
    simp

theorem neg_of_nat_mul_of_nat (m n : ℕ) : negOfNat m * ofNat n = negOfNat (m * n) := by
  rw [Int.mul_comm]
  simp [of_nat_mul_neg_of_nat, Nat.mul_comm]

theorem neg_succ_of_nat_mul_neg_of_nat (m : ℕ) : ∀ n, -[m+1] * negOfNat n = ofNat (succ m * n)
  | 0 => rfl
  | succ n => by
    unfold neg_of_nat
    simp

theorem neg_of_nat_mul_neg_succ_of_nat (m n : ℕ) : negOfNat n * -[m+1] = ofNat (n * succ m) := by
  rw [Int.mul_comm]
  simp [neg_succ_of_nat_mul_neg_of_nat, Nat.mul_comm]

attribute [local simp]
  of_nat_mul_neg_of_nat neg_of_nat_mul_of_nat neg_succ_of_nat_mul_neg_of_nat neg_of_nat_mul_neg_succ_of_nat

#print Int.mul_assoc /-
protected theorem mul_assoc : ∀ a b c : ℤ, a * b * c = a * (b * c)
  | of_nat m, of_nat n, of_nat k => by simp [Nat.mul_assoc]
  | of_nat m, of_nat n, -[k+1] => by simp [Nat.mul_assoc]
  | of_nat m, -[n+1], of_nat k => by simp [Nat.mul_assoc]
  | of_nat m, -[n+1], -[k+1] => by simp [Nat.mul_assoc]
  | -[m+1], of_nat n, of_nat k => by simp [Nat.mul_assoc]
  | -[m+1], of_nat n, -[k+1] => by simp [Nat.mul_assoc]
  | -[m+1], -[n+1], of_nat k => by simp [Nat.mul_assoc]
  | -[m+1], -[n+1], -[k+1] => by simp [Nat.mul_assoc]
-/

#print Int.mul_zero /-
protected theorem mul_zero : ∀ a : ℤ, a * 0 = 0
  | of_nat m => rfl
  | -[m+1] => rfl
-/

#print Int.zero_mul /-
protected theorem zero_mul (a : ℤ) : 0 * a = 0 :=
  Int.mul_comm a 0 ▸ Int.mul_zero a
-/

theorem neg_of_nat_eq_sub_nat_nat_zero : ∀ n, negOfNat n = subNatNat 0 n
  | 0 => rfl
  | succ n => rfl

theorem of_nat_mul_sub_nat_nat (m n k : ℕ) : ofNat m * subNatNat n k = subNatNat (m * n) (m * k) := by
  have h₀ : m > 0 ∨ 0 = m := Decidable.lt_or_eq_of_le m.zero_le
  cases' h₀ with h₀ h₀
  · have h := Nat.lt_or_ge n k
    cases' h with h h
    · have h' : m * n < m * k := Nat.mul_lt_mul_of_pos_left h h₀
      rw [sub_nat_nat_of_lt h, sub_nat_nat_of_lt h']
      simp
      rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]
      rw [← neg_of_nat_of_succ, Nat.mul_sub_left_distrib]
      rw [← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]
      rfl
      
    have h' : m * k ≤ m * n := Nat.mul_le_mul_left _ h
    rw [sub_nat_nat_of_le h, sub_nat_nat_of_le h']
    simp
    rw [Nat.mul_sub_left_distrib]
    
  have h₂ : of_nat 0 = 0 := rfl
  subst h₀
  simp [h₂, Int.zero_mul, Nat.zero_mul]

theorem neg_of_nat_add (m n : ℕ) : negOfNat m + negOfNat n = negOfNat (m + n) := by
  cases m
  · cases n
    · simp
      rfl
      
    simp [Nat.zero_add]
    rfl
    
  cases n
  · simp
    rfl
    
  simp [Nat.succ_add]
  rfl

theorem neg_succ_of_nat_mul_sub_nat_nat (m n k : ℕ) : -[m+1] * subNatNat n k = subNatNat (succ m * k) (succ m * n) := by
  have h := Nat.lt_or_ge n k
  cases' h with h h
  · have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
    rw [sub_nat_nat_of_lt h, sub_nat_nat_of_le (le_of_lt h')]
    simp [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h), Nat.mul_sub_left_distrib]
    
  have h' : n > k ∨ k = n := Decidable.lt_or_eq_of_le h
  cases' h' with h' h'
  · have h₁ : succ m * n > succ m * k := Nat.mul_lt_mul_of_pos_left h' (Nat.succ_pos m)
    rw [sub_nat_nat_of_le h, sub_nat_nat_of_lt h₁]
    simp [Nat.mul_sub_left_distrib, Nat.mul_comm]
    rw [Nat.mul_comm k, Nat.mul_comm n, ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁), ← neg_of_nat_of_succ]
    rfl
    
  subst h'
  simp
  rfl

attribute [local simp] of_nat_mul_sub_nat_nat neg_of_nat_add neg_succ_of_nat_mul_sub_nat_nat

protected theorem distrib_left : ∀ a b c : ℤ, a * (b + c) = a * b + a * c
  | of_nat m, of_nat n, of_nat k => by simp [Nat.left_distrib]
  | of_nat m, of_nat n, -[k+1] => by
    simp [neg_of_nat_eq_sub_nat_nat_zero]
    rw [← sub_nat_nat_add]
    rfl
  | of_nat m, -[n+1], of_nat k => by
    simp [neg_of_nat_eq_sub_nat_nat_zero]
    rw [Int.add_comm, ← sub_nat_nat_add]
    rfl
  | of_nat m, -[n+1], -[k+1] => by
    simp
    rw [← Nat.left_distrib, add_succ, succ_add]
  | -[m+1], of_nat n, of_nat k => by
    simp [Nat.mul_comm]
    rw [← Nat.right_distrib, Nat.mul_comm]
  | -[m+1], of_nat n, -[k+1] => by
    simp [neg_of_nat_eq_sub_nat_nat_zero]
    rw [Int.add_comm, ← sub_nat_nat_add]
    rfl
  | -[m+1], -[n+1], of_nat k => by
    simp [neg_of_nat_eq_sub_nat_nat_zero]
    rw [← sub_nat_nat_add]
    rfl
  | -[m+1], -[n+1], -[k+1] => by
    simp
    rw [← Nat.left_distrib, add_succ, succ_add]

protected theorem distrib_right (a b c : ℤ) : (a + b) * c = a * c + b * c := by
  rw [Int.mul_comm, Int.distrib_left]
  simp [Int.mul_comm]

#print Int.zero_ne_one /-
protected theorem zero_ne_one : (0 : Int) ≠ 1 := fun h : 0 = 1 => succ_ne_zero _ (Int.ofNat.inj h).symm
-/

theorem of_nat_sub {n m : ℕ} (h : m ≤ n) : ofNat (n - m) = ofNat n - ofNat m :=
  show ofNat (n - m) = ofNat n + negOfNat m from
    match m, h with
    | 0, h => rfl
    | succ m, h =>
      show ofNat (n - succ m) = subNatNat n (succ m) by delta sub_nat_nat <;> rw [Nat.sub_eq_zero_of_le h] <;> rfl

#print Int.add_left_comm /-
protected theorem add_left_comm (a b c : ℤ) : a + (b + c) = b + (a + c) := by
  rw [← Int.add_assoc, Int.add_comm a, Int.add_assoc]
-/

#print Int.add_left_cancel /-
protected theorem add_left_cancel {a b c : ℤ} (h : a + b = a + c) : b = c := by
  have : -a + (a + b) = -a + (a + c) := by rw [h]
  rwa [← Int.add_assoc, ← Int.add_assoc, Int.add_left_neg, Int.zero_add, Int.zero_add] at this
-/

#print Int.neg_add /-
protected theorem neg_add {a b : ℤ} : -(a + b) = -a + -b :=
  calc
    -(a + b) = -(a + b) + (a + b) + -a + -b := by
      rw [Int.add_assoc, Int.add_comm (-a), Int.add_assoc, Int.add_assoc, ← Int.add_assoc b]
      rw [Int.add_right_neg, Int.zero_add, Int.add_right_neg, Int.add_zero]
    _ = -a + -b := by rw [Int.add_left_neg, Int.zero_add]
    
-/

theorem neg_succ_of_nat_coe' (n : ℕ) : -[n+1] = -↑n - 1 := by rw [Int.sub_eq_add_neg, ← Int.neg_add] <;> rfl

#print Int.coe_nat_sub /-
protected theorem coe_nat_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n :=
  of_nat_sub
-/

attribute [local simp] Int.sub_eq_add_neg

protected theorem sub_nat_nat_eq_coe {m n : ℕ} : subNatNat m n = ↑m - ↑n :=
  sub_nat_nat_elim m n (fun m n i => i = ↑m - ↑n)
    (fun i n => by
      simp [Int.coe_nat_add, Int.add_left_comm, Int.add_assoc, Int.add_right_neg]
      rfl)
    fun i n => by
    rw [Int.coe_nat_add, Int.coe_nat_add, Int.coe_nat_one, Int.neg_succ_of_nat_eq, Int.sub_eq_add_neg, Int.neg_add,
      Int.neg_add, Int.neg_add, ← Int.add_assoc, ← Int.add_assoc, Int.add_right_neg, Int.zero_add]

#print Int.toNat /-
def toNat : ℤ → ℕ
  | (n : ℕ) => n
  | -[n+1] => 0
-/

theorem to_nat_sub (m n : ℕ) : toNat (m - n) = m - n := by
  rw [← Int.sub_nat_nat_eq_coe] <;>
    exact
      sub_nat_nat_elim m n (fun m n i => to_nat i = m - n) (fun i n => by rw [Nat.add_sub_cancel_left] <;> rfl)
        fun i n => by rw [Nat.add_assoc, Nat.sub_eq_zero_of_le (Nat.le_add_right _ _)] <;> rfl

#print Int.natMod /-
-- Since mod x y is always nonnegative when y ≠ 0, we can make a nat version of it
def natMod (m n : ℤ) : ℕ :=
  (m % n).toNat
-/

#print Int.one_mul /-
protected theorem one_mul : ∀ a : ℤ, (1 : ℤ) * a = a
  | of_nat n => show ofNat (1 * n) = ofNat n by rw [Nat.one_mul]
  | -[n+1] => show -[1 * n+1] = -[n+1] by rw [Nat.one_mul]
-/

#print Int.mul_one /-
protected theorem mul_one (a : ℤ) : a * 1 = a := by rw [Int.mul_comm, Int.one_mul]
-/

#print Int.neg_eq_neg_one_mul /-
protected theorem neg_eq_neg_one_mul : ∀ a : ℤ, -a = -1 * a
  | of_nat 0 => rfl
  | of_nat (n + 1) =>
    show _ = -[1 * n + 0+1] by
      rw [Nat.one_mul]
      rfl
  | -[n+1] =>
    show _ = ofNat _ by
      rw [Nat.one_mul]
      rfl
-/

theorem sign_mul_nat_abs : ∀ a : ℤ, sign a * natAbs a = a
  | (n + 1 : ℕ) => Int.one_mul _
  | 0 => rfl
  | -[n+1] => (Int.neg_eq_neg_one_mul _).symm

end Int

