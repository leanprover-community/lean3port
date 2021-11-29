prelude 
import Leanbin.Init.Data.Nat.Lemmas 
import Leanbin.Init.Meta.WellFoundedTactics

universe u

namespace Nat

def bodd_div2 : ℕ → Bool × ℕ
| 0 => (ff, 0)
| succ n =>
  match bodd_div2 n with 
  | (ff, m) => (tt, m)
  | (tt, m) => (ff, succ m)

def div2 (n : ℕ) : ℕ :=
  (bodd_div2 n).2

def bodd (n : ℕ) : Bool :=
  (bodd_div2 n).1

@[simp]
theorem bodd_zero : bodd 0 = ff :=
  rfl

theorem bodd_one : bodd 1 = tt :=
  rfl

theorem bodd_two : bodd 2 = ff :=
  rfl

@[simp]
theorem bodd_succ (n : ℕ) : bodd (succ n) = bnot (bodd n) :=
  by 
    unfold bodd bodd_div2 <;> cases bodd_div2 n <;> cases fst <;> rfl

@[simp]
theorem bodd_add (m n : ℕ) : bodd (m+n) = bxor (bodd m) (bodd n) :=
  by 
    induction' n with n IH
    ·
      simp 
      cases bodd m <;> rfl
    ·
      simp [add_succ, IH]
      cases bodd m <;> cases bodd n <;> rfl

@[simp]
theorem bodd_mul (m n : ℕ) : bodd (m*n) = (bodd m && bodd n) :=
  by 
    induction' n with n IH
    ·
      simp 
      cases bodd m <;> rfl
    ·
      simp [mul_succ, IH]
      cases bodd m <;> cases bodd n <;> rfl

-- error in Init.Data.Nat.Bitwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mod_two_of_bodd (n : exprℕ()) : «expr = »(«expr % »(n, 2), cond (bodd n) 1 0) :=
begin
  have [] [] [":=", expr congr_arg bodd (mod_add_div n 2)],
  simp [] [] [] ["[", expr bnot, "]"] [] ["at", ident this],
  rw ["[", expr show ∀
   b, «expr = »(«expr && »(ff, b), ff), by intros []; cases [expr b] []; refl, ",", expr show ∀
   b, «expr = »(bxor b ff, b), by intros []; cases [expr b] []; refl, "]"] ["at", ident this],
  rw ["[", "<-", expr this, "]"] [],
  cases [expr mod_two_eq_zero_or_one n] ["with", ident h, ident h]; rw [expr h] []; refl
end

@[simp]
theorem div2_zero : div2 0 = 0 :=
  rfl

theorem div2_one : div2 1 = 0 :=
  rfl

theorem div2_two : div2 2 = 1 :=
  rfl

@[simp]
theorem div2_succ (n : ℕ) : div2 (succ n) = cond (bodd n) (succ (div2 n)) (div2 n) :=
  by 
    unfold bodd div2 bodd_div2 <;> cases bodd_div2 n <;> cases fst <;> rfl

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

theorem bodd_add_div2 : ∀ n, (cond (bodd n) 1 0+2*div2 n) = n
| 0 => rfl
| succ n =>
  by 
    simp 
    refine' Eq.trans _ (congr_argₓ succ (bodd_add_div2 n))
    cases bodd n <;> simp [cond, bnot]
    ·
      rw [Nat.add_comm, Nat.zero_add]
    ·
      rw [succ_mul, Nat.add_comm 1, Nat.zero_add]

theorem div2_val n : div2 n = n / 2 :=
  by 
    refine'
      Nat.eq_of_mul_eq_mul_leftₓ
        (by 
          decide)
        (Nat.add_left_cancel (Eq.trans _ (Nat.mod_add_divₓ n 2).symm))
    rw [mod_two_of_bodd, bodd_add_div2]

def bit (b : Bool) : ℕ → ℕ :=
  cond b bit1 bit0

theorem bit0_val (n : Nat) : bit0 n = 2*n :=
  calc (n+n) = (0+n)+n :=
    by 
      rw [Nat.zero_add]
    _ = n*2 := rfl 
    _ = 2*n := Nat.mul_comm _ _
    

theorem bit1_val (n : Nat) : bit1 n = (2*n)+1 :=
  congr_argₓ succ (bit0_val _)

theorem bit_val b n : bit b n = (2*n)+cond b 1 0 :=
  by 
    cases b 
    apply bit0_val 
    apply bit1_val

theorem bit_decomp (n : Nat) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans$ (Nat.add_comm _ _).trans$ bodd_add_div2 _

def bit_cases_on {C : Nat → Sort u} n (h : ∀ b n, C (bit b n)) : C n :=
  by 
    rw [←bit_decomp n] <;> apply h

theorem bit_zero : bit ff 0 = 0 :=
  rfl

def shiftl' (b : Bool) (m : ℕ) : ℕ → ℕ
| 0 => m
| n+1 => bit b (shiftl' n)

def shiftl : ℕ → ℕ → ℕ :=
  shiftl' ff

@[simp]
theorem shiftl_zero m : shiftl m 0 = m :=
  rfl

@[simp]
theorem shiftl_succ m n : shiftl m (n+1) = bit0 (shiftl m n) :=
  rfl

def shiftr : ℕ → ℕ → ℕ
| m, 0 => m
| m, n+1 => div2 (shiftr m n)

def test_bit (m n : ℕ) : Bool :=
  bodd (shiftr m n)

-- error in Init.Data.Nat.Bitwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
def binary_rec {C : nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) : ∀ n, C n
| n := if n0 : «expr = »(n, 0) then by rw [expr n0] []; exact [expr z] else let n' := div2 n in
have «expr < »(n', n), begin
  change [expr «expr < »(div2 n, n)] [] [],
  rw [expr div2_val] [],
  apply [expr (div_lt_iff_lt_mul _ _ (succ_pos 1)).2],
  have [] [] [":=", expr nat.mul_lt_mul_of_pos_left (lt_succ_self 1) (lt_of_le_of_ne n.zero_le (ne.symm n0))],
  rwa [expr nat.mul_one] ["at", ident this]
end,
by rw ["[", "<-", expr show «expr = »(bit (bodd n) n', n), from bit_decomp n, "]"] []; exact [expr f (bodd n) n' (binary_rec n')]

def size : ℕ → ℕ :=
  binary_rec 0 fun _ _ => succ

def bits : ℕ → List Bool :=
  binary_rec [] fun b _ IH => b :: IH

def bitwise (f : Bool → Bool → Bool) : ℕ → ℕ → ℕ :=
  binary_rec (fun n => cond (f ff tt) n 0)
    fun a m Ia => binary_rec (cond (f tt ff) (bit a m) 0) fun b n _ => bit (f a b) (Ia n)

def lor : ℕ → ℕ → ℕ :=
  bitwise bor

def land : ℕ → ℕ → ℕ :=
  bitwise band

def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun a b => a && bnot b

def lxor : ℕ → ℕ → ℕ :=
  bitwise bxor

@[simp]
theorem binary_rec_zero {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) : binary_rec z f 0 = z :=
  by 
    rw [binary_rec]
    rfl

theorem bodd_bit b n : bodd (bit b n) = b :=
  by 
    rw [bit_val] <;> simp  <;> cases b <;> cases bodd n <;> rfl

theorem div2_bit b n : div2 (bit b n) = n :=
  by 
    rw [bit_val, div2_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add] <;>
      cases b <;>
        exact
          by 
            decide

theorem shiftl'_add b m n : ∀ k, shiftl' b m (n+k) = shiftl' b (shiftl' b m n) k
| 0 => rfl
| k+1 => congr_argₓ (bit b) (shiftl'_add k)

theorem shiftl_add : ∀ m n k, shiftl m (n+k) = shiftl (shiftl m n) k :=
  shiftl'_add _

theorem shiftr_add m n : ∀ k, shiftr m (n+k) = shiftr (shiftr m n) k
| 0 => rfl
| k+1 => congr_argₓ div2 (shiftr_add k)

theorem shiftl'_sub b m : ∀ {n k}, k ≤ n → shiftl' b m (n - k) = shiftr (shiftl' b m n) k
| n, 0, h => rfl
| n+1, k+1, h =>
  by 
    simp [shiftl']
    rw [Nat.add_comm, shiftr_add]
    simp [shiftr, div2_bit]
    apply shiftl'_sub (Nat.le_of_succ_le_succₓ h)

theorem shiftl_sub : ∀ m {n k}, k ≤ n → shiftl m (n - k) = shiftr (shiftl m n) k :=
  shiftl'_sub _

@[simp]
theorem test_bit_zero b n : test_bit (bit b n) 0 = b :=
  bodd_bit _ _

theorem test_bit_succ m b n : test_bit (bit b n) (succ m) = test_bit n m :=
  have  : bodd (shiftr (shiftr (bit b n) 1) m) = bodd (shiftr n m) :=
    by 
      dsimp [shiftr] <;> rw [div2_bit]
  by 
    rw [←shiftr_add, Nat.add_comm] at this <;> exact this

-- error in Init.Data.Nat.Bitwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem binary_rec_eq
{C : nat → Sort u}
{z : C 0}
{f : ∀ b n, C n → C (bit b n)}
(h : «expr = »(f ff 0 z, z))
(b n) : «expr = »(binary_rec z f (bit b n), f b n (binary_rec z f n)) :=
begin
  rw ["[", expr binary_rec, "]"] [],
  with_cases { by_cases [expr «expr = »(bit b n, 0)] },
  case [ident pos, ":", ident h'] { simp [] [] [] ["[", expr dif_pos h', "]"] [] [],
    generalize [] [":"] [expr «expr = »(binary_rec._main._pack._proof_1 (bit b n) h', e)],
    revert [ident e],
    have [ident bf] [] [":=", expr bodd_bit b n],
    have [ident n0] [] [":=", expr div2_bit b n],
    rw [expr h'] ["at", ident bf, ident n0],
    simp [] [] [] [] [] ["at", ident bf, ident n0],
    rw ["[", "<-", expr bf, ",", "<-", expr n0, ",", expr binary_rec_zero, "]"] [],
    intros [],
    exact [expr h.symm] },
  case [ident neg, ":", ident h'] { simp [] [] [] ["[", expr dif_neg h', "]"] [] [],
    generalize [] [":"] [expr «expr = »(binary_rec._main._pack._proof_2 (bit b n), e)],
    revert [ident e],
    rw ["[", expr bodd_bit, ",", expr div2_bit, "]"] [],
    intros [],
    refl }
end

theorem bitwise_bit_aux {f : Bool → Bool → Bool} (h : f ff ff = ff) :
  (@binary_rec (fun _ => ℕ) (cond (f tt ff) (bit ff 0) 0) fun b n _ => bit (f ff b) (cond (f ff tt) n 0)) =
    fun n : ℕ => cond (f ff tt) n 0 :=
  by 
    funext n 
    apply bit_cases_on n 
    intro b n 
    rw [binary_rec_eq]
    ·
      cases b <;>
        try 
            rw [h] <;>
          induction' fft : f ff tt with  <;> simp [cond] <;> rfl
    ·
      rw [h,
          show cond (f ff tt) 0 0 = 0 by 
            cases f ff tt <;> rfl,
          show cond (f tt ff) (bit ff 0) 0 = 0 by 
            cases f tt ff <;> rfl] <;>
        rfl

@[simp]
theorem bitwise_zero_left (f : Bool → Bool → Bool) n : bitwise f 0 n = cond (f ff tt) n 0 :=
  by 
    unfold bitwise <;> rw [binary_rec_zero]

@[simp]
theorem bitwise_zero_right (f : Bool → Bool → Bool) (h : f ff ff = ff) m : bitwise f m 0 = cond (f tt ff) m 0 :=
  by 
    unfold bitwise <;>
      apply bit_cases_on m <;> intros  <;> rw [binary_rec_eq, binary_rec_zero] <;> exact bitwise_bit_aux h

@[simp]
theorem bitwise_zero (f : Bool → Bool → Bool) : bitwise f 0 0 = 0 :=
  by 
    rw [bitwise_zero_left] <;> cases f ff tt <;> rfl

@[simp]
theorem bitwise_bit {f : Bool → Bool → Bool} (h : f ff ff = ff) a m b n :
  bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) :=
  by 
    unfold bitwise 
    rw [binary_rec_eq, binary_rec_eq]
    ·
      induction' ftf : f tt ff with  <;> dsimp [cond]
      rw
        [show f a ff = ff by 
          cases a <;> assumption]
      apply @congr_argₓ _ _ _ 0 (bit ff)
      runTac 
        tactic.swap 
      rw
        [show f a ff = a by 
          cases a <;> assumption]
      apply congr_argₓ (bit a)
      all_goals 
        apply bit_cases_on m 
        intro a m 
        rw [binary_rec_eq, binary_rec_zero]
        rw [←bitwise_bit_aux h, ftf]
        rfl
    ·
      exact bitwise_bit_aux h

theorem bitwise_swap {f : Bool → Bool → Bool} (h : f ff ff = ff) :
  bitwise (Function.swap f) = Function.swap (bitwise f) :=
  by 
    funext m n 
    revert n 
    dsimp [Function.swap]
    apply binary_rec _ (fun a m' IH => _) m <;> intro n
    ·
      rw [bitwise_zero_left, bitwise_zero_right]
      exact h 
    apply bit_cases_on n <;> intro b n' 
    rw [bitwise_bit, bitwise_bit, IH] <;> exact h

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
theorem test_bit_bitwise {f : Bool → Bool → Bool} (h : f ff ff = ff) m n k :
  test_bit (bitwise f m n) k = f (test_bit m k) (test_bit n k) :=
  by 
    revert m n <;>
      induction' k with k IH <;>
        intro m n <;> apply bit_cases_on m <;> intro a m' <;> apply bit_cases_on n <;> intro b n' <;> rw [bitwise_bit h]
    ·
      simp [test_bit_zero]
    ·
      simp [test_bit_succ, IH]

@[simp]
theorem test_bit_lor : ∀ m n k, test_bit (lor m n) k = (test_bit m k || test_bit n k) :=
  test_bit_bitwise rfl

@[simp]
theorem test_bit_land : ∀ m n k, test_bit (land m n) k = (test_bit m k && test_bit n k) :=
  test_bit_bitwise rfl

@[simp]
theorem test_bit_ldiff : ∀ m n k, test_bit (ldiff m n) k = (test_bit m k && bnot (test_bit n k)) :=
  test_bit_bitwise rfl

@[simp]
theorem test_bit_lxor : ∀ m n k, test_bit (lxor m n) k = bxor (test_bit m k) (test_bit n k) :=
  test_bit_bitwise rfl

end Nat

