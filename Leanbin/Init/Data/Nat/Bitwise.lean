/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

! This file was ported from Lean 3 source module init.data.nat.bitwise
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Meta.WellFoundedTactics

universe u

namespace Nat

#print Nat.boddDiv2 /-
def boddDiv2 : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | succ n =>
    match bodd_div2 n with
    | (ff, m) => (true, m)
    | (tt, m) => (false, succ m)
#align nat.bodd_div2 Nat.boddDiv2
-/

#print Nat.div2 /-
def div2 (n : ℕ) : ℕ :=
  (boddDiv2 n).2
#align nat.div2 Nat.div2
-/

#print Nat.bodd /-
def bodd (n : ℕ) : Bool :=
  (boddDiv2 n).1
#align nat.bodd Nat.bodd
-/

#print Nat.bodd_zero /-
@[simp]
theorem bodd_zero : bodd 0 = ff :=
  rfl
#align nat.bodd_zero Nat.bodd_zero
-/

#print Nat.bodd_one /-
theorem bodd_one : bodd 1 = tt :=
  rfl
#align nat.bodd_one Nat.bodd_one
-/

#print Nat.bodd_two /-
theorem bodd_two : bodd 2 = ff :=
  rfl
#align nat.bodd_two Nat.bodd_two
-/

#print Nat.bodd_succ /-
@[simp]
theorem bodd_succ (n : ℕ) : bodd (succ n) = not (bodd n) := by
  unfold bodd bodd_div2 <;> cases bodd_div2 n <;> cases fst <;> rfl
#align nat.bodd_succ Nat.bodd_succ
-/

#print Nat.bodd_add /-
@[simp]
theorem bodd_add (m n : ℕ) : bodd (m + n) = xor (bodd m) (bodd n) :=
  by
  induction' n with n IH
  · simp
    cases bodd m <;> rfl
  · simp [add_succ, IH]
    cases bodd m <;> cases bodd n <;> rfl
#align nat.bodd_add Nat.bodd_add
-/

#print Nat.bodd_mul /-
@[simp]
theorem bodd_mul (m n : ℕ) : bodd (m * n) = (bodd m && bodd n) :=
  by
  induction' n with n IH
  · simp
    cases bodd m <;> rfl
  · simp [mul_succ, IH]
    cases bodd m <;> cases bodd n <;> rfl
#align nat.bodd_mul Nat.bodd_mul
-/

#print Nat.mod_two_of_bodd /-
theorem mod_two_of_bodd (n : ℕ) : n % 2 = cond (bodd n) 1 0 :=
  by
  have := congr_arg bodd (mod_add_div n 2)
  simp [not] at this
  rw [show ∀ b, (ff && b) = ff by intros <;> cases b <;> rfl,
    show ∀ b, xor b ff = b by intros <;> cases b <;> rfl] at this
  rw [← this]
  cases' mod_two_eq_zero_or_one n with h h <;> rw [h] <;> rfl
#align nat.mod_two_of_bodd Nat.mod_two_of_bodd
-/

#print Nat.div2_zero /-
@[simp]
theorem div2_zero : div2 0 = 0 :=
  rfl
#align nat.div2_zero Nat.div2_zero
-/

#print Nat.div2_one /-
theorem div2_one : div2 1 = 0 :=
  rfl
#align nat.div2_one Nat.div2_one
-/

#print Nat.div2_two /-
theorem div2_two : div2 2 = 1 :=
  rfl
#align nat.div2_two Nat.div2_two
-/

#print Nat.div2_succ /-
@[simp]
theorem div2_succ (n : ℕ) : div2 (succ n) = cond (bodd n) (succ (div2 n)) (div2 n) := by
  unfold bodd div2 bodd_div2 <;> cases bodd_div2 n <;> cases fst <;> rfl
#align nat.div2_succ Nat.div2_succ
-/

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

#print Nat.bodd_add_div2 /-
theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | 0 => rfl
  | succ n => by
    simp
    refine' Eq.trans _ (congr_arg succ (bodd_add_div2 n))
    cases bodd n <;> simp [cond, not]
    · rw [Nat.add_comm, Nat.zero_add]
    · rw [succ_mul, Nat.add_comm 1, Nat.zero_add]
#align nat.bodd_add_div2 Nat.bodd_add_div2
-/

#print Nat.div2_val /-
theorem div2_val (n) : div2 n = n / 2 :=
  by
  refine'
    Nat.eq_of_mul_eq_mul_left (by decide)
      (Nat.add_left_cancel (Eq.trans _ (Nat.mod_add_div n 2).symm))
  rw [mod_two_of_bodd, bodd_add_div2]
#align nat.div2_val Nat.div2_val
-/

#print Nat.bit /-
def bit (b : Bool) : ℕ → ℕ :=
  cond b bit1 bit0
#align nat.bit Nat.bit
-/

#print Nat.bit0_val /-
theorem bit0_val (n : Nat) : bit0 n = 2 * n :=
  calc
    n + n = 0 + n + n := by rw [Nat.zero_add]
    _ = n * 2 := rfl
    _ = 2 * n := Nat.mul_comm _ _
    
#align nat.bit0_val Nat.bit0_val
-/

#print Nat.bit1_val /-
theorem bit1_val (n : Nat) : bit1 n = 2 * n + 1 :=
  congr_arg succ (bit0_val _)
#align nat.bit1_val Nat.bit1_val
-/

#print Nat.bit_val /-
theorem bit_val (b n) : bit b n = 2 * n + cond b 1 0 :=
  by
  cases b
  apply bit0_val
  apply bit1_val
#align nat.bit_val Nat.bit_val
-/

#print Nat.bit_decomp /-
theorem bit_decomp (n : Nat) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (Nat.add_comm _ _).trans <| bodd_add_div2 _
#align nat.bit_decomp Nat.bit_decomp
-/

#print Nat.bitCasesOn /-
def bitCasesOn {C : Nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := by
  rw [← bit_decomp n] <;> apply h
#align nat.bit_cases_on Nat.bitCasesOn
-/

#print Nat.bit_zero /-
theorem bit_zero : bit false 0 = 0 :=
  rfl
#align nat.bit_zero Nat.bit_zero
-/

#print Nat.shiftl' /-
def shiftl' (b : Bool) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => bit b (shiftl' n)
#align nat.shiftl' Nat.shiftl'
-/

#print Nat.shiftl /-
def shiftl : ℕ → ℕ → ℕ :=
  shiftl' false
#align nat.shiftl Nat.shiftl
-/

#print Nat.shiftl_zero /-
@[simp]
theorem shiftl_zero (m) : shiftl m 0 = m :=
  rfl
#align nat.shiftl_zero Nat.shiftl_zero
-/

#print Nat.shiftl_succ /-
@[simp]
theorem shiftl_succ (m n) : shiftl m (n + 1) = bit0 (shiftl m n) :=
  rfl
#align nat.shiftl_succ Nat.shiftl_succ
-/

#print Nat.shiftr /-
def shiftr : ℕ → ℕ → ℕ
  | m, 0 => m
  | m, n + 1 => div2 (shiftr m n)
#align nat.shiftr Nat.shiftr
-/

#print Nat.testBit /-
def testBit (m n : ℕ) : Bool :=
  bodd (shiftr m n)
#align nat.test_bit Nat.testBit
-/

#print Nat.binaryRec /-
def binaryRec {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) : ∀ n, C n
  | n =>
    if n0 : n = 0 then by rw [n0] <;> exact z
    else by
      let n' := div2 n
      have : n' < n := by
        change div2 n < n; rw [div2_val]
        apply (div_lt_iff_lt_mul <| succ_pos 1).2
        have := Nat.mul_lt_mul_of_pos_left (lt_succ_self 1) (lt_of_le_of_ne n.zero_le (Ne.symm n0))
        rwa [Nat.mul_one] at this
      rw [← show bit (bodd n) n' = n from bit_decomp n] <;> exact f (bodd n) n' (binary_rec n')
#align nat.binary_rec Nat.binaryRec
-/

#print Nat.size /-
def size : ℕ → ℕ :=
  binaryRec 0 fun _ _ => succ
#align nat.size Nat.size
-/

#print Nat.bits /-
def bits : ℕ → List Bool :=
  binaryRec [] fun b _ IH => b :: IH
#align nat.bits Nat.bits
-/

#print Nat.bitwise /-
def bitwise (f : Bool → Bool → Bool) : ℕ → ℕ → ℕ :=
  binaryRec (fun n => cond (f false true) n 0) fun a m Ia =>
    binaryRec (cond (f true false) (bit a m) 0) fun b n _ => bit (f a b) (Ia n)
#align nat.bitwise Nat.bitwise
-/

#print Nat.lor /-
def lor : ℕ → ℕ → ℕ :=
  bitwise or
#align nat.lor Nat.lor
-/

#print Nat.land /-
def land : ℕ → ℕ → ℕ :=
  bitwise and
#align nat.land Nat.land
-/

#print Nat.ldiff' /-
def ldiff' : ℕ → ℕ → ℕ :=
  bitwise fun a b => a && not b
#align nat.ldiff Nat.ldiff'
-/

#print Nat.lxor' /-
def lxor' : ℕ → ℕ → ℕ :=
  bitwise xor
#align nat.lxor Nat.lxor'
-/

#print Nat.binaryRec_zero /-
@[simp]
theorem binaryRec_zero {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) :
    binaryRec z f 0 = z := by
  rw [binary_rec]
  rfl
#align nat.binary_rec_zero Nat.binaryRec_zero
-/

/-! bitwise ops -/


#print Nat.bodd_bit /-
theorem bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val] <;> simp <;> cases b <;> cases bodd n <;> rfl
#align nat.bodd_bit Nat.bodd_bit
-/

#print Nat.div2_bit /-
theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add] <;> cases b <;>
    exact by decide
#align nat.div2_bit Nat.div2_bit
-/

#print Nat.shiftl'_add /-
theorem shiftl'_add (b m n) : ∀ k, shiftl' b m (n + k) = shiftl' b (shiftl' b m n) k
  | 0 => rfl
  | k + 1 => congr_arg (bit b) (shiftl'_add k)
#align nat.shiftl'_add Nat.shiftl'_add
-/

#print Nat.shiftl_add /-
theorem shiftl_add : ∀ m n k, shiftl m (n + k) = shiftl (shiftl m n) k :=
  shiftl'_add _
#align nat.shiftl_add Nat.shiftl_add
-/

#print Nat.shiftr_add /-
theorem shiftr_add (m n) : ∀ k, shiftr m (n + k) = shiftr (shiftr m n) k
  | 0 => rfl
  | k + 1 => congr_arg div2 (shiftr_add k)
#align nat.shiftr_add Nat.shiftr_add
-/

#print Nat.shiftl'_sub /-
theorem shiftl'_sub (b m) : ∀ {n k}, k ≤ n → shiftl' b m (n - k) = shiftr (shiftl' b m n) k
  | n, 0, h => rfl
  | n + 1, k + 1, h => by
    simp [shiftl']; rw [Nat.add_comm, shiftr_add]
    simp [shiftr, div2_bit]
    apply shiftl'_sub (Nat.le_of_succ_le_succ h)
#align nat.shiftl'_sub Nat.shiftl'_sub
-/

#print Nat.shiftl_sub /-
theorem shiftl_sub : ∀ (m) {n k}, k ≤ n → shiftl m (n - k) = shiftr (shiftl m n) k :=
  shiftl'_sub _
#align nat.shiftl_sub Nat.shiftl_sub
-/

#print Nat.testBit_zero /-
@[simp]
theorem testBit_zero (b n) : testBit (bit b n) 0 = b :=
  bodd_bit _ _
#align nat.test_bit_zero Nat.testBit_zero
-/

#print Nat.testBit_succ /-
theorem testBit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m :=
  by
  have : bodd (shiftr (shiftr (bit b n) 1) m) = bodd (shiftr n m) := by
    dsimp [shiftr] <;> rw [div2_bit]
  rw [← shiftr_add, Nat.add_comm] at this <;> exact this
#align nat.test_bit_succ Nat.testBit_succ
-/

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:145:2: warning: unsupported: with_cases -/
#print Nat.binaryRec_eq /-
theorem binaryRec_eq {C : Nat → Sort u} {z : C 0} {f : ∀ b n, C n → C (bit b n)}
    (h : f false 0 z = z) (b n) : binaryRec z f (bit b n) = f b n (binaryRec z f n) :=
  by
  rw [binary_rec]
  by_cases bit b n = 0
  case pos h' =>
    simp [dif_pos h']
    generalize binary_rec._main._pack._proof_1 (bit b n) h' = e
    revert e
    have bf := bodd_bit b n
    have n0 := div2_bit b n
    rw [h'] at bf n0
    simp at bf n0
    rw [← bf, ← n0, binary_rec_zero]
    intros ; exact h.symm
  case neg h' =>
    simp [dif_neg h']
    generalize binary_rec._main._pack._proof_2 (bit b n) = e
    revert e
    rw [bodd_bit, div2_bit]
    intros ; rfl
#align nat.binary_rec_eq Nat.binaryRec_eq
-/

#print Nat.bitwise'_bit_aux /-
theorem bitwise'_bit_aux {f : Bool → Bool → Bool} (h : f false false = ff) :
    (@binaryRec (fun _ => ℕ) (cond (f true false) (bit false 0) 0) fun b n _ =>
        bit (f false b) (cond (f false true) n 0)) =
      fun n : ℕ => cond (f false true) n 0 :=
  by
  funext n
  apply bit_cases_on n; intro b n; rw [binary_rec_eq]
  · cases b <;> try rw [h] <;> induction' fft : f ff tt with <;> simp [cond] <;> rfl
  ·
    rw [h, show cond (f ff tt) 0 0 = 0 by cases f ff tt <;> rfl,
        show cond (f tt ff) (bit ff 0) 0 = 0 by cases f tt ff <;> rfl] <;>
      rfl
#align nat.bitwise_bit_aux Nat.bitwise'_bit_aux
-/

/- warning: nat.bitwise_zero_left -> Nat.bitwise'_zero_left is a dubious translation:
lean 3 declaration is
  forall (f : Bool -> Bool -> Bool) (n : Nat), Eq.{1} Nat (Nat.bitwise f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) (cond.{0} Nat (f Bool.false Bool.true) n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall (f : Bool -> Bool -> Bool) (n : Nat), Eq.{1} Nat (Nat.bitwise' f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (cond.{0} Nat (f Bool.false Bool.true) n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align nat.bitwise_zero_left Nat.bitwise'_zero_leftₓ'. -/
@[simp]
theorem bitwise'_zero_left (f : Bool → Bool → Bool) (n) : bitwise f 0 n = cond (f false true) n 0 :=
  by unfold bitwise <;> rw [binary_rec_zero]
#align nat.bitwise_zero_left Nat.bitwise'_zero_left

/- warning: nat.bitwise_zero_right -> Nat.bitwise'_zero_right is a dubious translation:
lean 3 declaration is
  forall (f : Bool -> Bool -> Bool), (Eq.{1} Bool (f Bool.false Bool.false) Bool.false) -> (forall (m : Nat), Eq.{1} Nat (Nat.bitwise f m (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (cond.{0} Nat (f Bool.true Bool.false) m (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))
but is expected to have type
  forall (f : Bool -> Bool -> Bool), (Eq.{1} Bool (f Bool.false Bool.false) Bool.false) -> (forall (m : Nat), Eq.{1} Nat (Nat.bitwise' f m (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (cond.{0} Nat (f Bool.true Bool.false) m (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
Case conversion may be inaccurate. Consider using '#align nat.bitwise_zero_right Nat.bitwise'_zero_rightₓ'. -/
@[simp]
theorem bitwise'_zero_right (f : Bool → Bool → Bool) (h : f false false = ff) (m) :
    bitwise f m 0 = cond (f true false) m 0 := by
  unfold bitwise <;> apply bit_cases_on m <;> intros <;> rw [binary_rec_eq, binary_rec_zero] <;>
    exact bitwise_bit_aux h
#align nat.bitwise_zero_right Nat.bitwise'_zero_right

/- warning: nat.bitwise_zero -> Nat.bitwise'_zero is a dubious translation:
lean 3 declaration is
  forall (f : Bool -> Bool -> Bool), Eq.{1} Nat (Nat.bitwise f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall (f : Bool -> Bool -> Bool), Eq.{1} Nat (Nat.bitwise' f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align nat.bitwise_zero Nat.bitwise'_zeroₓ'. -/
@[simp]
theorem bitwise'_zero (f : Bool → Bool → Bool) : bitwise f 0 0 = 0 := by
  rw [bitwise_zero_left] <;> cases f ff tt <;> rfl
#align nat.bitwise_zero Nat.bitwise'_zero

/- warning: nat.bitwise_bit -> Nat.bitwise'_bit is a dubious translation:
lean 3 declaration is
  forall {f : Bool -> Bool -> Bool}, (Eq.{1} Bool (f Bool.false Bool.false) Bool.false) -> (forall (a : Bool) (m : Nat) (b : Bool) (n : Nat), Eq.{1} Nat (Nat.bitwise f (Nat.bit a m) (Nat.bit b n)) (Nat.bit (f a b) (Nat.bitwise f m n)))
but is expected to have type
  forall {f : Bool -> Bool -> Bool}, (Eq.{1} Bool (f Bool.false Bool.false) Bool.false) -> (forall (a : Bool) (m : Nat) (b : Bool) (n : Nat), Eq.{1} Nat (Nat.bitwise' f (Nat.bit a m) (Nat.bit b n)) (Nat.bit (f a b) (Nat.bitwise' f m n)))
Case conversion may be inaccurate. Consider using '#align nat.bitwise_bit Nat.bitwise'_bitₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.swap -/
@[simp]
theorem bitwise'_bit {f : Bool → Bool → Bool} (h : f false false = ff) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) :=
  by
  unfold bitwise
  rw [binary_rec_eq, binary_rec_eq]
  · induction' ftf : f tt ff with <;> dsimp [cond]
    rw [show f a ff = ff by cases a <;> assumption]
    apply @congr_arg _ _ _ 0 (bit ff)
    run_tac
      tactic.swap
    rw [show f a ff = a by cases a <;> assumption]
    apply congr_arg (bit a)
    all_goals
      apply bit_cases_on m; intro a m
      rw [binary_rec_eq, binary_rec_zero]
      rw [← bitwise_bit_aux h, ftf]; rfl
  · exact bitwise_bit_aux h
#align nat.bitwise_bit Nat.bitwise'_bit

/- warning: nat.bitwise_swap -> Nat.bitwise'_swap is a dubious translation:
lean 3 declaration is
  forall {f : Bool -> Bool -> Bool}, (Eq.{1} Bool (f Bool.false Bool.false) Bool.false) -> (Eq.{1} (Nat -> Nat -> Nat) (Nat.bitwise (Function.swap.{1, 1, 1} Bool Bool (fun (ᾰ : Bool) (ᾰ : Bool) => Bool) f)) (Function.swap.{1, 1, 1} Nat Nat (fun (ᾰ : Nat) (ᾰ : Nat) => Nat) (Nat.bitwise f)))
but is expected to have type
  forall {f : Bool -> Bool -> Bool}, (Eq.{1} Bool (f Bool.false Bool.false) Bool.false) -> (Eq.{1} (Nat -> Nat -> Nat) (Nat.bitwise' (Function.swap.{1, 1, 1} Bool Bool (fun (ᾰ : Bool) (ᾰ : Bool) => Bool) f)) (Function.swap.{1, 1, 1} Nat Nat (fun (ᾰ : Nat) (ᾰ : Nat) => Nat) (Nat.bitwise' f)))
Case conversion may be inaccurate. Consider using '#align nat.bitwise_swap Nat.bitwise'_swapₓ'. -/
theorem bitwise'_swap {f : Bool → Bool → Bool} (h : f false false = ff) :
    bitwise (Function.swap f) = Function.swap (bitwise f) :=
  by
  funext m n; revert n
  dsimp [Function.swap]
  apply binary_rec _ (fun a m' IH => _) m <;> intro n
  · rw [bitwise_zero_left, bitwise_zero_right]
    exact h
  apply bit_cases_on n <;> intro b n'
  rw [bitwise_bit, bitwise_bit, IH] <;> exact h
#align nat.bitwise_swap Nat.bitwise'_swap

/- warning: nat.lor_bit -> Nat.lor'_bit is a dubious translation:
lean 3 declaration is
  forall (a : Bool) (m : Nat) (b : Bool) (n : Nat), Eq.{1} Nat (Nat.lor (Nat.bit a m) (Nat.bit b n)) (Nat.bit (or a b) (Nat.lor m n))
but is expected to have type
  forall (a : Bool) (m : Nat) (b : Bool) (n : Nat), Eq.{1} Nat (Nat.lor' (Nat.bit a m) (Nat.bit b n)) (Nat.bit (or a b) (Nat.lor' m n))
Case conversion may be inaccurate. Consider using '#align nat.lor_bit Nat.lor'_bitₓ'. -/
@[simp]
theorem lor'_bit : ∀ a m b n, lor (bit a m) (bit b n) = bit (a || b) (lor m n) :=
  bitwise'_bit rfl
#align nat.lor_bit Nat.lor'_bit

/- warning: nat.land_bit -> Nat.land'_bit is a dubious translation:
lean 3 declaration is
  forall (a : Bool) (m : Nat) (b : Bool) (n : Nat), Eq.{1} Nat (Nat.land (Nat.bit a m) (Nat.bit b n)) (Nat.bit (and a b) (Nat.land m n))
but is expected to have type
  forall (a : Bool) (m : Nat) (b : Bool) (n : Nat), Eq.{1} Nat (Nat.land' (Nat.bit a m) (Nat.bit b n)) (Nat.bit (and a b) (Nat.land' m n))
Case conversion may be inaccurate. Consider using '#align nat.land_bit Nat.land'_bitₓ'. -/
@[simp]
theorem land'_bit : ∀ a m b n, land (bit a m) (bit b n) = bit (a && b) (land m n) :=
  bitwise'_bit rfl
#align nat.land_bit Nat.land'_bit

#print Nat.ldiff'_bit /-
@[simp]
theorem ldiff'_bit : ∀ a m b n, ldiff' (bit a m) (bit b n) = bit (a && not b) (ldiff' m n) :=
  bitwise'_bit rfl
#align nat.ldiff_bit Nat.ldiff'_bit
-/

#print Nat.lxor'_bit /-
@[simp]
theorem lxor'_bit : ∀ a m b n, lxor' (bit a m) (bit b n) = bit (xor a b) (lxor' m n) :=
  bitwise'_bit rfl
#align nat.lxor_bit Nat.lxor'_bit
-/

/- warning: nat.test_bit_bitwise -> Nat.testBit_bitwise' is a dubious translation:
lean 3 declaration is
  forall {f : Bool -> Bool -> Bool}, (Eq.{1} Bool (f Bool.false Bool.false) Bool.false) -> (forall (m : Nat) (n : Nat) (k : Nat), Eq.{1} Bool (Nat.testBit (Nat.bitwise f m n) k) (f (Nat.testBit m k) (Nat.testBit n k)))
but is expected to have type
  forall {f : Bool -> Bool -> Bool}, (Eq.{1} Bool (f Bool.false Bool.false) Bool.false) -> (forall (m : Nat) (n : Nat) (k : Nat), Eq.{1} Bool (Nat.testBit (Nat.bitwise' f m n) k) (f (Nat.testBit m k) (Nat.testBit n k)))
Case conversion may be inaccurate. Consider using '#align nat.test_bit_bitwise Nat.testBit_bitwise'ₓ'. -/
@[simp]
theorem testBit_bitwise' {f : Bool → Bool → Bool} (h : f false false = ff) (m n k) :
    testBit (bitwise f m n) k = f (testBit m k) (testBit n k) :=
  by
  revert m n <;> induction' k with k IH <;> intro m n <;> apply bit_cases_on m <;> intro a m' <;>
        apply bit_cases_on n <;>
      intro b n' <;>
    rw [bitwise_bit h]
  · simp [test_bit_zero]
  · simp [test_bit_succ, IH]
#align nat.test_bit_bitwise Nat.testBit_bitwise'

/- warning: nat.test_bit_lor -> Nat.testBit_lor' is a dubious translation:
lean 3 declaration is
  forall (m : Nat) (n : Nat) (k : Nat), Eq.{1} Bool (Nat.testBit (Nat.lor m n) k) (or (Nat.testBit m k) (Nat.testBit n k))
but is expected to have type
  forall (m : Nat) (n : Nat) (k : Nat), Eq.{1} Bool (Nat.testBit (Nat.lor' m n) k) (or (Nat.testBit m k) (Nat.testBit n k))
Case conversion may be inaccurate. Consider using '#align nat.test_bit_lor Nat.testBit_lor'ₓ'. -/
@[simp]
theorem testBit_lor' : ∀ m n k, testBit (lor m n) k = (testBit m k || testBit n k) :=
  testBit_bitwise' rfl
#align nat.test_bit_lor Nat.testBit_lor'

/- warning: nat.test_bit_land -> Nat.testBit_land' is a dubious translation:
lean 3 declaration is
  forall (m : Nat) (n : Nat) (k : Nat), Eq.{1} Bool (Nat.testBit (Nat.land m n) k) (and (Nat.testBit m k) (Nat.testBit n k))
but is expected to have type
  forall (m : Nat) (n : Nat) (k : Nat), Eq.{1} Bool (Nat.testBit (Nat.land' m n) k) (and (Nat.testBit m k) (Nat.testBit n k))
Case conversion may be inaccurate. Consider using '#align nat.test_bit_land Nat.testBit_land'ₓ'. -/
@[simp]
theorem testBit_land' : ∀ m n k, testBit (land m n) k = (testBit m k && testBit n k) :=
  testBit_bitwise' rfl
#align nat.test_bit_land Nat.testBit_land'

#print Nat.testBit_ldiff' /-
@[simp]
theorem testBit_ldiff' : ∀ m n k, testBit (ldiff' m n) k = (testBit m k && not (testBit n k)) :=
  testBit_bitwise' rfl
#align nat.test_bit_ldiff Nat.testBit_ldiff'
-/

#print Nat.testBit_lxor' /-
@[simp]
theorem testBit_lxor' : ∀ m n k, testBit (lxor' m n) k = xor (testBit m k) (testBit n k) :=
  testBit_bitwise' rfl
#align nat.test_bit_lxor Nat.testBit_lxor'
-/

end Nat

