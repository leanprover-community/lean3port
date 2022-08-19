/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
prelude
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Meta.WellFoundedTactics
import Leanbin.Init.Data.Bool.Lemmas

universe u

namespace Nat

def boddDiv2 : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | succ n =>
    match boddDiv2 n with
    | (false, m) => (true, m)
    | (true, m) => (false, succ m)

def div2 (n : ℕ) : ℕ :=
  (boddDiv2 n).2

def bodd (n : ℕ) : Bool :=
  (boddDiv2 n).1

@[simp]
theorem bodd_zero : bodd 0 = false :=
  rfl

theorem bodd_one : bodd 1 = true :=
  rfl

theorem bodd_two : bodd 2 = false :=
  rfl

@[simp]
theorem bodd_succ (n : ℕ) : bodd (succ n) = bnot (bodd n) := by
  simp [bodd, boddDiv2] <;> split <;> simp_all

@[simp]
theorem bodd_add (m n : ℕ) : bodd (m + n) = bxor (bodd m) (bodd n) := by
  induction n <;> simp_all [add_succ]

@[simp]
theorem bodd_mul (m n : ℕ) : bodd (m * n) = (bodd m && bodd n) := by
  induction' n with n IH
  · simp
  · simp [mul_succ, IH]
    cases bodd m <;> cases bodd n <;> rfl

theorem mod_two_of_bodd (n : ℕ) : n % 2 = cond (bodd n) 1 0 := by
  rw [← congr_arg bodd (mod_add_div n 2)]
  cases mod_two_eq_zero_or_one n <;>
    simp_all [bodd_add, bodd_mul]

@[simp]
theorem div2_zero : div2 0 = 0 :=
  rfl

theorem div2_one : div2 1 = 0 :=
  rfl

theorem div2_two : div2 2 = 1 :=
  rfl

@[simp]
theorem div2_succ (n : ℕ) : div2 (succ n) = cond (bodd n) (succ (div2 n)) (div2 n) := by
  simp only [div2, bodd, boddDiv2] <;> cases boddDiv2 n with | mk f s => cases f <;> simp

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | 0 => rfl
  | succ n => by
    simp
    refine' Eq.trans _ (congr_arg succ (bodd_add_div2 n))
    cases bodd n <;> simp [cond, bnot]
    · simp [Nat.succ_eq_one_add]
    · simp (config := {arith:=true}) [Nat.succ_mul, Nat.succ_eq_one_add]

theorem div2_val (n) : div2 n = n / 2 := by
  refine'
    Nat.eq_of_mul_eq_mul_left
      (by
        decide)
      (Nat.add_left_cancel (Eq.trans _ (Nat.mod_add_div n 2).symm))
  rw [mod_two_of_bodd, bodd_add_div2]

def bit (b : Bool) : ℕ → ℕ :=
  cond b bit1 bit0

theorem bit0_val (n : Nat) : bit0 n = 2 * n :=
  calc
    n + n = 0 + n + n := by
      rw [Nat.zero_add]
    _ = n * 2 := rfl
    _ = 2 * n := Nat.mul_comm _ _
    

theorem bit1_val (n : Nat) : bit1 n = 2 * n + 1 :=
  congr_arg succ (bit0_val _)

theorem bit_val (b n) : bit b n = 2 * n + cond b 1 0 := by
  cases b
  apply bit0_val
  apply bit1_val

theorem bit_decomp (n : Nat) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (Nat.add_comm _ _).trans <| bodd_add_div2 _

@[elabAsElim]
def bitCasesOn {C : Nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := by
  rw [← bit_decomp n] <;> apply h

theorem bit_zero : bit false 0 = 0 :=
  rfl

theorem bit_eq_zero_iff : bit b n = 0 ↔ b = false ∧ n = 0 := by
  cases b <;> cases n <;> simp [bit, Nat.bit1_ne_zero, bit0, Nat.add_succ]

def shiftl' (b : Bool) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => bit b (shiftl' b m n)

def shiftl : ℕ → ℕ → ℕ :=
  shiftl' false

@[simp]
theorem shiftl_zero (m) : shiftl m 0 = m :=
  rfl

@[simp]
theorem shiftl_succ (m n) : shiftl m (n + 1) = bit0 (shiftl m n) :=
  rfl

def shiftr : ℕ → ℕ → ℕ
  | m, 0 => m
  | m, n + 1 => div2 (shiftr m n)

def testBit (m n : ℕ) : Bool :=
  bodd (shiftr m n)

@[elabAsElim]
def binaryRec {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) (n) : C n :=
    if n0 : n = 0 then
      n0 ▸ z
    else
      let n' := div2 n
      have : n' < n := by
        change div2 n < n
        rw [div2_val]
        apply (div_lt_iff_lt_mul <| succ_pos 1).2
        have := Nat.mul_lt_mul_of_pos_left (lt_succ_self 1) (lt_of_le_of_ne n.zero_le (Ne.symm n0))
        rwa [Nat.mul_one] at this
      bit_decomp n ▸ f (bodd n) n' (binaryRec z f n')

def size : ℕ → ℕ :=
  binaryRec 0 fun _ _ => succ

def bits : ℕ → List Bool :=
  binaryRec [] fun b _ IH => b :: IH

def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun a b => a && bnot b

def lxor : ℕ → ℕ → ℕ :=
  bitwise bxor

@[simp]
theorem binary_rec_zero {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) : binaryRec z f 0 = z := by
  rw [binaryRec]
  rfl

-- bitwise ops
theorem bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val] <;> simp <;> cases b <;> cases bodd n <;> rfl

theorem bit_mod_two : bit b n % 2 = cond b 1 0 := by
  rw [mod_two_of_bodd, bodd_bit]

theorem bit_mod_two_eq_one : bit b n % 2 = 1 ↔ b := by
  cases b <;> simp [bit_mod_two]

theorem bit_mod_two_eq_zero : bit b n % 2 = 0 ↔ ¬ b := by
  cases b <;> simp [bit_mod_two]

@[simp]
theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add] <;>
    cases b <;>
      exact by
        decide

@[simp]
theorem bit_div_two : bit b n / 2 = n := by
  rw [← div2_val, div2_bit]

theorem shiftl'_add (b m n) : ∀ k, shiftl' b m (n + k) = shiftl' b (shiftl' b m n) k
  | 0 => rfl
  | k + 1 => congr_arg (bit b) (shiftl'_add b m n k)

theorem shiftl_add : ∀ m n k, shiftl m (n + k) = shiftl (shiftl m n) k :=
  shiftl'_add _

theorem shiftr_add (m n) : ∀ k, shiftr m (n + k) = shiftr (shiftr m n) k
  | 0 => rfl
  | k + 1 => congr_arg div2 (shiftr_add m n k)

theorem shiftr_bit_succ : shiftr (bit b m) (k + 1) = shiftr m k := by
  rw [add_comm, shiftr_add, shiftr, shiftr, div2_bit]

theorem shiftl'_sub (b m) : ∀ {n k}, k ≤ n → shiftl' b m (n - k) = shiftr (shiftl' b m n) k
  | n, 0, h => rfl
  | n + 1, k + 1, h => by
    simp only [shiftl']
    rw [shiftr_add, Nat.add_sub_add_right, shiftl'_sub b m (Nat.le_of_succ_le_succ h)]
    simp only [Nat.add, ← shiftr_add, shiftr_bit_succ]

theorem shiftl_sub : ∀ (m) {n k}, k ≤ n → shiftl m (n - k) = shiftr (shiftl m n) k :=
  shiftl'_sub _

@[simp]
theorem test_bit_zero (b n) : testBit (bit b n) 0 = b :=
  bodd_bit _ _

theorem test_bit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m := by
  have : bodd (shiftr (shiftr (bit b n) 1) m) = bodd (shiftr n m) := by
    dsimp [shiftr] <;> rw [div2_bit]
  rw [← shiftr_add, Nat.add_comm] at this <;> exact this

set_option pp.proofs true
theorem binary_rec_eq {C : Nat → Sort u} {z : C 0} {f : ∀ b n, C n → C (bit b n)} (h : f false 0 z = z) (b n) :
    binaryRec z f (bit b n) = f b n (binaryRec z f n) := by
  rw [binaryRec]
  by_cases h' : bit b n = 0
  case pos =>
    simp [dif_pos h']
    have bf := bodd_bit b n
    have n0 := div2_bit b n
    rw [h'] at bf n0
    simp at bf n0
    subst bf
    subst n0
    simp [binary_rec_zero]
    exact h.symm
  case neg =>
    simp [dif_neg h']
    generalize bit_decomp (bit b n) = e
    revert e
    rw [bodd_bit, div2_bit]
    simp

@[simp]
theorem bitwise_zero_left (f : Bool → Bool → Bool) (n) : bitwise f 0 n = cond (f false true) n 0 := by
  unfold bitwise
  simp only [cond]
  cases f false true <;> simp

@[simp]
theorem bitwise_zero_right (f : Bool → Bool → Bool) (m) :
    bitwise f m 0 = cond (f true false) m 0 := by
  unfold bitwise
  split <;> split <;> (try split) <;> simp_all

@[simp]
theorem bitwise_zero (f : Bool → Bool → Bool) : bitwise f 0 0 = 0 := by
  rw [bitwise_zero_left] <;> cases f false true <;> rfl

@[simp]
theorem bitwise_bit {f : Bool → Bool → Bool} (h : f false false = false) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  conv => lhs; unfold bitwise
  simp only [bit_div_two, bit_eq_zero_iff, bit_mod_two_eq_one,
    fun n : Nat => show n + n = bit false n from rfl,
    fun n : Nat => show n + n + 1 = bit true n from rfl]
  cases a <;> cases b <;> simp <;> split <;> (try split) <;> (try split) <;> simp_all [bit, bit1]

theorem bitwise_swap {f : Bool → Bool → Bool} (h : f false false = false) :
    bitwise (Function.swap f) = Function.swap (bitwise f) := by
  funext m n; revert n
  refine binaryRec ?zero (fun a m' IH n => ?bit) m
  case zero => simp
  case bit =>
    refine bitCasesOn n fun b n' => ?_
    simp [bitwise_bit, h, IH]

@[simp]
theorem lor_bit : ∀ a m b n, lor (bit a m) (bit b n) = bit (a || b) (lor m n) :=
  bitwise_bit rfl

@[simp]
theorem land_bit : ∀ a m b n, land (bit a m) (bit b n) = bit (a && b) (land m n) :=
  bitwise_bit rfl

@[simp]
theorem ldiff_bit : ∀ a m b n, ldiff (bit a m) (bit b n) = bit (a && bnot b) (ldiff m n) :=
  bitwise_bit rfl

@[simp]
theorem lxor_bit : ∀ a m b n, lxor (bit a m) (bit b n) = bit (bxor a b) (lxor m n) :=
  bitwise_bit rfl

@[simp]
theorem test_bit_bitwise {f : Bool → Bool → Bool} (h : f false false = false) (m n k) :
    testBit (bitwise f m n) k = f (testBit m k) (testBit n k) := by
  induction k generalizing m n
    <;> refine bitCasesOn m fun bm m => ?_
    <;> refine bitCasesOn n fun bn n => ?_
    <;> simp_all [bitwise_bit h, test_bit_succ]

@[simp]
theorem test_bit_lor : ∀ m n k, testBit (lor m n) k = (testBit m k || testBit n k) :=
  test_bit_bitwise rfl

@[simp]
theorem test_bit_land : ∀ m n k, testBit (land m n) k = (testBit m k && testBit n k) :=
  test_bit_bitwise rfl

@[simp]
theorem test_bit_ldiff : ∀ m n k, testBit (ldiff m n) k = (testBit m k && bnot (testBit n k)) :=
  test_bit_bitwise rfl

@[simp]
theorem test_bit_lxor : ∀ m n k, testBit (lxor m n) k = bxor (testBit m k) (testBit n k) :=
  test_bit_bitwise rfl

end Nat

