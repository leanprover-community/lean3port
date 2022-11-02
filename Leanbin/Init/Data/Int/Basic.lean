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

-- the type, coercions, and notation
inductive Int : Type
  | of_nat : Nat → Int
  | neg_succ_of_nat : Nat → Int
  deriving DecidableEq

instance : Coe Nat Int :=
  ⟨Int.ofNat⟩

protected def Int.repr : Int → String
  | Int.ofNat n => repr n
  | Int.negSucc n => "-" ++ repr (succ n)

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

-- definitions of basic functions
def negOfNat : ℕ → ℤ
  | 0 => 0
  | succ m => -[1 + m]

def subNatNat (m n : ℕ) : ℤ :=
  match (n - m : Nat) with
  | 0 => ofNat (m - n)
  |-- m ≥ n
      succ
      k =>
    -[1 + k]

-- m < n, and n - m = succ k
theorem sub_nat_nat_of_sub_eq_zero {m n : ℕ} (h : n - m = 0) : subNatNat m n = ofNat (m - n) := by
  unfold sub_nat_nat
  rw [h]
  unfold sub_nat_nat._match_1

theorem sub_nat_nat_of_sub_eq_succ {m n k : ℕ} (h : n - m = succ k) : subNatNat m n = -[1 + k] := by
  unfold sub_nat_nat
  rw [h]
  unfold sub_nat_nat._match_1

protected def neg : ℤ → ℤ
  | of_nat n => negOfNat n
  | -[1 + n] => succ n

protected def add : ℤ → ℤ → ℤ
  | of_nat m, of_nat n => ofNat (m + n)
  | of_nat m, -[1 + n] => subNatNat m (succ n)
  | -[1 + m], of_nat n => subNatNat n (succ m)
  | -[1 + m], -[1 + n] => -[1 + succ (m + n)]

protected def mul : ℤ → ℤ → ℤ
  | of_nat m, of_nat n => ofNat (m * n)
  | of_nat m, -[1 + n] => negOfNat (m * succ n)
  | -[1 + m], of_nat n => negOfNat (succ m * n)
  | -[1 + m], -[1 + n] => ofNat (succ m * succ n)

instance : Neg ℤ :=
  ⟨Int.neg⟩

instance : Add ℤ :=
  ⟨Int.add⟩

instance : Mul ℤ :=
  ⟨Int.mul⟩

-- defeq to algebra.sub which gives subtraction for arbitrary `add_group`s
protected def sub : ℤ → ℤ → ℤ := fun m n => m + -n

instance : Sub ℤ :=
  ⟨Int.sub⟩

protected theorem neg_zero : -(0 : ℤ) = 0 :=
  rfl

theorem of_nat_add (n m : ℕ) : ofNat (n + m) = ofNat n + ofNat m :=
  rfl

theorem of_nat_mul (n m : ℕ) : ofNat (n * m) = ofNat n * ofNat m :=
  rfl

theorem of_nat_succ (n : ℕ) : ofNat (succ n) = ofNat n + 1 :=
  rfl

theorem neg_of_nat_zero : -ofNat 0 = 0 :=
  rfl

theorem neg_of_nat_of_succ (n : ℕ) : -ofNat (succ n) = -[1 + n] :=
  rfl

theorem neg_neg_of_nat_succ (n : ℕ) : - -[1 + n] = ofNat (succ n) :=
  rfl

theorem of_nat_eq_coe (n : ℕ) : ofNat n = ↑n :=
  rfl

theorem neg_succ_of_nat_coe (n : ℕ) : -[1 + n] = -↑(n + 1) :=
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

theorem of_nat_add_neg_succ_of_nat (m n : Nat) : ofNat m + -[1 + n] = subNatNat m (succ n) :=
  rfl

theorem neg_succ_of_nat_add_of_nat (m n : Nat) : -[1 + m] + ofNat n = subNatNat n (succ m) :=
  rfl

theorem neg_succ_of_nat_add_neg_succ_of_nat (m n : Nat) : -[1 + m] + -[1 + n] = -[1 + succ (m + n)] :=
  rfl

theorem of_nat_mul_of_nat (m n : Nat) : ofNat m * ofNat n = ofNat (m * n) :=
  rfl

theorem of_nat_mul_neg_succ_of_nat (m n : Nat) : ofNat m * -[1 + n] = negOfNat (m * succ n) :=
  rfl

theorem neg_succ_of_nat_of_nat (m n : Nat) : -[1 + m] * ofNat n = negOfNat (succ m * n) :=
  rfl

theorem mul_neg_succ_of_nat_neg_succ_of_nat (m n : Nat) : -[1 + m] * -[1 + n] = ofNat (succ m * succ n) :=
  rfl

attribute [local simp]
  of_nat_add_of_nat of_nat_mul_of_nat neg_of_nat_zero neg_of_nat_of_succ neg_neg_of_nat_succ of_nat_add_neg_succ_of_nat neg_succ_of_nat_add_of_nat neg_succ_of_nat_add_neg_succ_of_nat of_nat_mul_neg_succ_of_nat neg_succ_of_nat_of_nat mul_neg_succ_of_nat_neg_succ_of_nat

-- some basic functions and properties
protected theorem coe_nat_inj {m n : ℕ} (h : (↑m : ℤ) = ↑n) : m = n :=
  Int.ofNat.inj h

theorem of_nat_eq_of_nat_iff (m n : ℕ) : ofNat m = ofNat n ↔ m = n :=
  Iff.intro Int.ofNat.inj (congr_arg _)

protected theorem coe_nat_eq_coe_nat_iff (m n : ℕ) : (↑m : ℤ) = ↑n ↔ m = n :=
  of_nat_eq_of_nat_iff m n

theorem neg_succ_of_nat_inj_iff {m n : ℕ} : negSucc m = negSucc n ↔ m = n :=
  ⟨negSucc.inj, fun H => by simp [H]⟩

theorem neg_succ_of_nat_eq (n : ℕ) : -[1 + n] = -(n + 1) :=
  rfl

-- neg
protected theorem neg_neg : ∀ a : ℤ, - -a = a
  | of_nat 0 => rfl
  | of_nat (n + 1) => rfl
  | -[1 + n] => rfl

/- warning: int.neg_inj -> Int.neg_inj is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (Eq.{1} Int (Neg.neg.{0} Int Int.hasNeg a) (Neg.neg.{0} Int Int.hasNeg b)) -> (Eq.{1} Int a b)
but is expected to have type
  forall {a : Int} {b : Int}, Iff (Eq.{1} Int (Neg.neg.{0} Int Int.instNegInt a) (Neg.neg.{0} Int Int.instNegInt b)) (Eq.{1} Int a b)
Case conversion may be inaccurate. Consider using '#align int.neg_inj Int.neg_injₓ'. -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_inj [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_=_» («term-_» "-" `a) "=" («term-_» "-" `b))] [] ")")]
       (Term.typeSpec ":" («term_=_» `a "=" `b)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule ["←"] (Term.app `Int.neg_neg [`a]))
              ","
              (Tactic.rwRule ["←"] (Term.app `Int.neg_neg [`b]))
              ","
              (Tactic.rwRule [] `h)]
             "]")
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] (Term.app `Int.neg_neg [`a]))
             ","
             (Tactic.rwRule ["←"] (Term.app `Int.neg_neg [`b]))
             ","
             (Tactic.rwRule [] `h)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] (Term.app `Int.neg_neg [`a]))
         ","
         (Tactic.rwRule ["←"] (Term.app `Int.neg_neg [`b]))
         ","
         (Tactic.rwRule [] `h)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.neg_neg [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.neg_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected theorem neg_inj { a b : ℤ } ( h : - a = - b ) : a = b := by rw [ ← Int.neg_neg a , ← Int.neg_neg b , h ]

protected theorem sub_eq_add_neg {a b : ℤ} : a - b = a + -b :=
  rfl

-- basic properties of sub_nat_nat
theorem sub_nat_nat_elim (m n : ℕ) (P : ℕ → ℕ → ℤ → Prop) (hp : ∀ i n, P (n + i) n (ofNat i))
    (hn : ∀ i m, P m (m + i + 1) (-[1 + i])) : P m n (subNatNat m n) := by
  have H : ∀ k, n - m = k → P m n (Nat.casesOn k (of_nat (m - n)) fun a => -[1 + a]) := by
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

theorem sub_nat_nat_of_lt {m n : ℕ} (h : m < n) : subNatNat m n = -[1 + pred (n - m)] := by
  have : n - m = succ (pred (n - m)) := Eq.symm (succ_pred_eq_of_pos (Nat.sub_pos_of_lt h))
  rw [sub_nat_nat_of_sub_eq_succ this]

-- nat_abs
@[simp]
def natAbs : ℤ → ℕ
  | of_nat m => m
  | -[1 + m] => succ m

theorem nat_abs_of_nat (n : ℕ) : natAbs ↑n = n :=
  rfl

theorem eq_zero_of_nat_abs_eq_zero : ∀ {a : ℤ}, natAbs a = 0 → a = 0
  | of_nat m, H => congr_arg ofNat H
  | -[1 + m'], H => absurd H (succ_ne_zero _)

theorem nat_abs_pos_of_ne_zero {a : ℤ} (h : a ≠ 0) : 0 < natAbs a :=
  (Nat.eq_zero_or_pos _).resolve_left <| mt eq_zero_of_nat_abs_eq_zero h

theorem nat_abs_zero : natAbs (0 : Int) = (0 : Nat) :=
  rfl

theorem nat_abs_one : natAbs (1 : Int) = (1 : Nat) :=
  rfl

theorem nat_abs_mul_self : ∀ {a : ℤ}, ↑(natAbs a * natAbs a) = a * a
  | of_nat m => rfl
  | -[1 + m'] => rfl

@[simp]
theorem nat_abs_neg (a : ℤ) : natAbs (-a) = natAbs a := by
  cases' a with n n
  cases n <;> rfl
  rfl

theorem nat_abs_eq : ∀ a : ℤ, a = natAbs a ∨ a = -natAbs a
  | of_nat m => Or.inl rfl
  | -[1 + m'] => Or.inr rfl

theorem eq_coe_or_neg (a : ℤ) : ∃ n : ℕ, a = n ∨ a = -n :=
  ⟨_, nat_abs_eq a⟩

-- sign
def sign : ℤ → ℤ
  | (n + 1 : ℕ) => 1
  | 0 => 0
  | -[1 + n] => -1

@[simp]
theorem sign_zero : sign 0 = 0 :=
  rfl

@[simp]
theorem sign_one : sign 1 = 1 :=
  rfl

@[simp]
theorem sign_neg_one : sign (-1) = -1 :=
  rfl

-- Quotient and remainder 
-- There are three main conventions for integer division,
-- referred here as the E, F, T rounding conventions.
-- All three pairs satisfy the identity x % y + (x / y) * y = x
-- unconditionally.
-- E-rounding: This pair satisfies 0 ≤ mod x y < nat_abs y for y ≠ 0
protected def div : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => ofNat (m / n)
  | (m : ℕ), -[1 + n] => -ofNat (m / succ n)
  | -[1 + m], 0 => 0
  | -[1 + m], (n + 1 : ℕ) => -[1 + m / succ n]
  | -[1 + m], -[1 + n] => ofNat (succ (m / succ n))

protected def mod : ℤ → ℤ → ℤ
  | (m : ℕ), n => (m % natAbs n : ℕ)
  | -[1 + m], n => subNatNat (natAbs n) (succ (m % natAbs n))

-- F-rounding: This pair satisfies fdiv x y = floor (x / y)
def fdiv : ℤ → ℤ → ℤ
  | 0, _ => 0
  | (m : ℕ), (n : ℕ) => ofNat (m / n)
  | (m + 1 : ℕ), -[1 + n] => -[1 + m / succ n]
  | -[1 + m], 0 => 0
  | -[1 + m], (n + 1 : ℕ) => -[1 + m / succ n]
  | -[1 + m], -[1 + n] => ofNat (succ m / succ n)

def fmod : ℤ → ℤ → ℤ
  | 0, _ => 0
  | (m : ℕ), (n : ℕ) => ofNat (m % n)
  | (m + 1 : ℕ), -[1 + n] => subNatNat (m % succ n) n
  | -[1 + m], (n : ℕ) => subNatNat n (succ (m % n))
  | -[1 + m], -[1 + n] => -ofNat (succ m % succ n)

-- T-rounding: This pair satisfies quot x y = round_to_zero (x / y)
def quot : ℤ → ℤ → ℤ
  | of_nat m, of_nat n => ofNat (m / n)
  | of_nat m, -[1 + n] => -ofNat (m / succ n)
  | -[1 + m], of_nat n => -ofNat (succ m / n)
  | -[1 + m], -[1 + n] => ofNat (succ m / succ n)

def rem : ℤ → ℤ → ℤ
  | of_nat m, of_nat n => ofNat (m % n)
  | of_nat m, -[1 + n] => ofNat (m % succ n)
  | -[1 + m], of_nat n => -ofNat (succ m % n)
  | -[1 + m], -[1 + n] => -ofNat (succ m % succ n)

instance : Div ℤ :=
  ⟨Int.div⟩

instance : Mod ℤ :=
  ⟨Int.mod⟩

-- gcd
def gcd (m n : ℤ) : ℕ :=
  gcd (natAbs m) (natAbs n)

/-
   int is a ring
-/
-- addition
protected theorem add_comm : ∀ a b : ℤ, a + b = b + a
  | of_nat n, of_nat m => by simp [Nat.add_comm]
  | of_nat n, -[1 + m] => rfl
  | -[1 + n], of_nat m => rfl
  | -[1 + n], -[1 + m] => by simp [Nat.add_comm]

protected theorem add_zero : ∀ a : ℤ, a + 0 = a
  | of_nat n => rfl
  | -[1 + n] => rfl

protected theorem zero_add (a : ℤ) : 0 + a = a :=
  Int.add_comm a 0 ▸ Int.add_zero a

theorem sub_nat_nat_sub {m n : ℕ} (h : n ≤ m) (k : ℕ) : subNatNat (m - n) k = subNatNat m (k + n) :=
  calc
    subNatNat (m - n) k = subNatNat (m - n + n) (k + n) := by rw [sub_nat_nat_add_add]
    _ = subNatNat m (k + n) := by rw [Nat.sub_add_cancel h]
    

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in transitivity #[[]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `sub_nat_nat_add [])
      (Command.declSig
       [(Term.explicitBinder "(" [`m `n `k] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `subNatNat [(«term_+_» `m "+" `n) `k])
         "="
         («term_+_» (Term.app `ofNat [`m]) "+" (Term.app `subNatNat [`n `k])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `le_or_lt [`k `n]))))
           []
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `h)]
            []
            ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h']))] "]")
               [])
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h₂ []]
                 [(Term.typeSpec ":" («term_≤_» `k "≤" («term_+_» `m "+" `n)))]
                 ":="
                 (Term.app `le_trans [`h' (Term.app `Nat.le_add_left [(Term.hole "_") (Term.hole "_")])]))))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h₂]))] "]")
               [])
              [])
             (group (Tactic.simp "simp" [] [] [] [] []) [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Nat.add_sub_assoc [`h']))] "]")
               [])
              [])])
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h']))] "]") [])
           []
           (Tactic.simp "simp" [] [] [] [] [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])]))]
             "]")
            [])
           []
           (choice
            (Tactic.trace
             "trace"
             (str
              "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in transitivity #[[]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg\""))
            (Tactic.traceMessage
             "trace"
             (str
              "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in transitivity #[[]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg\"")))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule ["←"] (Term.app `Nat.sub_add_cancel [(Term.app `le_of_lt [`h'])]))]
             "]")
            [])
           []
           (Tactic.apply "apply" `sub_nat_nat_add_add)])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `le_or_lt [`k `n]))))
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `h)]
           []
           ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h']))] "]")
              [])
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h₂ []]
                [(Term.typeSpec ":" («term_≤_» `k "≤" («term_+_» `m "+" `n)))]
                ":="
                (Term.app `le_trans [`h' (Term.app `Nat.le_add_left [(Term.hole "_") (Term.hole "_")])]))))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h₂]))] "]")
              [])
             [])
            (group (Tactic.simp "simp" [] [] [] [] []) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Nat.add_sub_assoc [`h']))] "]")
              [])
             [])])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h']))] "]") [])
          []
          (Tactic.simp "simp" [] [] [] [] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])]))]
            "]")
           [])
          []
          (choice
           (Tactic.trace
            "trace"
            (str
             "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in transitivity #[[]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg\""))
           (Tactic.traceMessage
            "trace"
            (str
             "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in transitivity #[[]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg\"")))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] (Term.app `Nat.sub_add_cancel [(Term.app `le_of_lt [`h'])]))]
            "]")
           [])
          []
          (Tactic.apply "apply" `sub_nat_nat_add_add)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `sub_nat_nat_add_add)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_nat_nat_add_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `Nat.sub_add_cancel [(Term.app `le_of_lt [`h'])]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.sub_add_cancel [(Term.app `le_of_lt [`h'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_lt [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_of_lt [`h']) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.sub_add_cancel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  sub_nat_nat_add
  ( m n k : ℕ ) : subNatNat m + n k = ofNat m + subNatNat n k
  :=
    by
      have h := le_or_lt k n
        cases' h with h' h'
        ·
          rw [ sub_nat_nat_of_le h' ]
            have h₂ : k ≤ m + n := le_trans h' Nat.le_add_left _ _
            rw [ sub_nat_nat_of_le h₂ ]
            simp
            rw [ Nat.add_sub_assoc h' ]
        rw [ sub_nat_nat_of_lt h' ]
        simp
        rw [ succ_pred_eq_of_pos Nat.sub_pos_of_lt h' ]
        trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in transitivity #[[]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in transitivity #[[]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
        rw [ ← Nat.sub_add_cancel le_of_lt h' ]
        apply sub_nat_nat_add_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `sub_nat_nat_add_neg_succ_of_nat [])
      (Command.declSig
       [(Term.explicitBinder "(" [`m `n `k] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_» (Term.app `subNatNat [`m `n]) "+" («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]")))
         "="
         (Term.app `subNatNat [`m («term_+_» `n "+" (Term.app `succ [`k]))]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `le_or_lt [`n `m]))))
           []
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `h)]
            []
            ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h']))] "]")
               [])
              [])
             (group (Tactic.simp "simp" [] [] [] [] []) [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `sub_nat_nat_sub [`h'])) "," (Tactic.rwRule [] `Nat.add_comm)]
                "]")
               [])
              [])])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₂ []]
              [(Term.typeSpec ":" («term_<_» `m "<" («term_+_» `n "+" (Term.app `succ [`k]))))]
              ":="
              (Term.app `Nat.lt_of_lt_of_le [`h' (Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₃ []]
              [(Term.typeSpec ":" («term_≤_» `m "≤" («term_+_» `n "+" `k)))]
              ":="
              (Term.app `le_of_succ_le_succ [`h₂]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h']))
              ","
              (Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h₂]))]
             "]")
            [])
           []
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Nat.add_comm)] "]"] [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule ["←"] `add_succ)
              ","
              (Tactic.rwRule [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])]))
              ","
              (Tactic.rwRule [] `add_succ)
              ","
              (Tactic.rwRule [] (Term.app `succ_sub [`h₃]))
              ","
              (Tactic.rwRule [] `pred_succ)]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `Nat.add_comm [`n]))
              ","
              (Tactic.rwRule [] (Term.app `Nat.add_sub_assoc [(Term.app `le_of_lt [`h'])]))]
             "]")
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `le_or_lt [`n `m]))))
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `h)]
           []
           ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h']))] "]")
              [])
             [])
            (group (Tactic.simp "simp" [] [] [] [] []) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `sub_nat_nat_sub [`h'])) "," (Tactic.rwRule [] `Nat.add_comm)]
               "]")
              [])
             [])])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₂ []]
             [(Term.typeSpec ":" («term_<_» `m "<" («term_+_» `n "+" (Term.app `succ [`k]))))]
             ":="
             (Term.app `Nat.lt_of_lt_of_le [`h' (Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₃ []]
             [(Term.typeSpec ":" («term_≤_» `m "≤" («term_+_» `n "+" `k)))]
             ":="
             (Term.app `le_of_succ_le_succ [`h₂]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h']))
             ","
             (Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h₂]))]
            "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Nat.add_comm)] "]"] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `add_succ)
             ","
             (Tactic.rwRule [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])]))
             ","
             (Tactic.rwRule [] `add_succ)
             ","
             (Tactic.rwRule [] (Term.app `succ_sub [`h₃]))
             ","
             (Tactic.rwRule [] `pred_succ)]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `Nat.add_comm [`n]))
             ","
             (Tactic.rwRule [] (Term.app `Nat.add_sub_assoc [(Term.app `le_of_lt [`h'])]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `Nat.add_comm [`n]))
         ","
         (Tactic.rwRule [] (Term.app `Nat.add_sub_assoc [(Term.app `le_of_lt [`h'])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.add_sub_assoc [(Term.app `le_of_lt [`h'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_lt [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_of_lt [`h']) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.add_sub_assoc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.add_comm [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `add_succ)
         ","
         (Tactic.rwRule [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])]))
         ","
         (Tactic.rwRule [] `add_succ)
         ","
         (Tactic.rwRule [] (Term.app `succ_sub [`h₃]))
         ","
         (Tactic.rwRule [] `pred_succ)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pred_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `succ_sub [`h₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succ_sub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.sub_pos_of_lt [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.sub_pos_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Nat.sub_pos_of_lt [`h']) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succ_pred_eq_of_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  sub_nat_nat_add_neg_succ_of_nat
  ( m n k : ℕ ) : subNatNat m n + - [ 1 + k ] = subNatNat m n + succ k
  :=
    by
      have h := le_or_lt n m
        cases' h with h' h'
        · rw [ sub_nat_nat_of_le h' ] simp rw [ sub_nat_nat_sub h' , Nat.add_comm ]
        have h₂ : m < n + succ k := Nat.lt_of_lt_of_le h' Nat.le_add_right _ _
        have h₃ : m ≤ n + k := le_of_succ_le_succ h₂
        rw [ sub_nat_nat_of_lt h' , sub_nat_nat_of_lt h₂ ]
        simp [ Nat.add_comm ]
        rw [ ← add_succ , succ_pred_eq_of_pos Nat.sub_pos_of_lt h' , add_succ , succ_sub h₃ , pred_succ ]
        rw [ Nat.add_comm n , Nat.add_sub_assoc le_of_lt h' ]

theorem add_assoc_aux1 (m n : ℕ) : ∀ c : ℤ, ofNat m + ofNat n + c = ofNat m + (ofNat n + c)
  | of_nat k => by simp [Nat.add_assoc]
  | -[1 + k] => by simp [sub_nat_nat_add]

theorem add_assoc_aux2 (m n k : ℕ) : -[1 + m] + -[1 + n] + ofNat k = -[1 + m] + (-[1 + n] + ofNat k) := by
  simp [add_succ]
  rw [Int.add_comm, sub_nat_nat_add_neg_succ_of_nat]
  simp [add_succ, succ_add, Nat.add_comm]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_assoc [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`a `b `c]
         [(Term.typeSpec ":" (Int.termℤ "ℤ"))]
         ","
         («term_=_» («term_+_» («term_+_» `a "+" `b) "+" `c) "=" («term_+_» `a "+" («term_+_» `b "+" `c))))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.app `of_nat [`m]) "," (Term.app `of_nat [`n]) "," `c]]
           "=>"
           (Term.app `add_assoc_aux1 [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(Term.app `of_nat [`m]) "," `b "," (Term.app `of_nat [`k])]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Int.add_comm)
                  ","
                  (Tactic.rwRule ["←"] `add_assoc_aux1)
                  ","
                  (Tactic.rwRule [] (Term.app `Int.add_comm [(Term.app `of_nat [`k])]))
                  ","
                  (Tactic.rwRule [] `add_assoc_aux1)
                  ","
                  (Tactic.rwRule [] (Term.app `Int.add_comm [`b]))]
                 "]")
                [])]))))
          (Term.matchAlt
           "|"
           [[`a "," (Term.app `of_nat [`n]) "," (Term.app `of_nat [`k])]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Int.add_comm)
                  ","
                  (Tactic.rwRule [] (Term.app `Int.add_comm [`a]))
                  ","
                  (Tactic.rwRule ["←"] `add_assoc_aux1)
                  ","
                  (Tactic.rwRule [] (Term.app `Int.add_comm [`a]))
                  ","
                  (Tactic.rwRule [] (Term.app `Int.add_comm [(Term.app `of_nat [`k])]))]
                 "]")
                [])]))))
          (Term.matchAlt
           "|"
           [[(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]"))
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `n)] "]"))
             ","
             (Term.app `of_nat [`k])]]
           "=>"
           (Term.app `add_assoc_aux2 [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]"))
             ","
             (Term.app `of_nat [`n])
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Int.add_comm)
                  ","
                  (Tactic.rwRule ["←"] `add_assoc_aux2)
                  ","
                  (Tactic.rwRule [] (Term.app `Int.add_comm [(Term.app `of_nat [`n])]))
                  ","
                  (Tactic.rwRule ["←"] `add_assoc_aux2)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `Int.add_comm [(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]"))]))]
                 "]")
                [])]))))
          (Term.matchAlt
           "|"
           [[(Term.app `of_nat [`m])
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `n)] "]"))
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Int.add_comm)
                  ","
                  (Tactic.rwRule [] (Term.app `Int.add_comm [(Term.app `of_nat [`m])]))
                  ","
                  (Tactic.rwRule [] (Term.app `Int.add_comm [(Term.app `of_nat [`m])]))
                  ","
                  (Tactic.rwRule ["←"] `add_assoc_aux2)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `Int.add_comm [(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))]))]
                 "]")
                [])]))))
          (Term.matchAlt
           "|"
           [[(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]"))
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `n)] "]"))
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] `add_succ)
                  ","
                  (Tactic.simpLemma [] [] `Nat.add_comm)
                  ","
                  (Tactic.simpLemma [] [] `Nat.add_left_comm)
                  ","
                  (Tactic.simpLemma [] [] `neg_of_nat_of_succ)]
                 "]"]
                [])]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `add_succ)
             ","
             (Tactic.simpLemma [] [] `Nat.add_comm)
             ","
             (Tactic.simpLemma [] [] `Nat.add_left_comm)
             ","
             (Tactic.simpLemma [] [] `neg_of_nat_of_succ)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `add_succ)
         ","
         (Tactic.simpLemma [] [] `Nat.add_comm)
         ","
         (Tactic.simpLemma [] [] `Nat.add_left_comm)
         ","
         (Tactic.simpLemma [] [] `neg_of_nat_of_succ)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_of_nat_of_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.add_left_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (num "1") "+" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `n)] "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(«term_+_» (num "1") "+" `n)] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (num "1") "+" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (num "1") "+" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Int.add_comm)
             ","
             (Tactic.rwRule [] (Term.app `Int.add_comm [(Term.app `of_nat [`m])]))
             ","
             (Tactic.rwRule [] (Term.app `Int.add_comm [(Term.app `of_nat [`m])]))
             ","
             (Tactic.rwRule ["←"] `add_assoc_aux2)
             ","
             (Tactic.rwRule
              []
              (Term.app `Int.add_comm [(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Int.add_comm)
         ","
         (Tactic.rwRule [] (Term.app `Int.add_comm [(Term.app `of_nat [`m])]))
         ","
         (Tactic.rwRule [] (Term.app `Int.add_comm [(Term.app `of_nat [`m])]))
         ","
         (Tactic.rwRule ["←"] `add_assoc_aux2)
         ","
         (Tactic.rwRule
          []
          (Term.app `Int.add_comm [(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.add_comm [(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (num "1") "+" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     [(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]")) []]
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_assoc_aux2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    add_assoc
    : ∀ a b c : ℤ , a + b + c = a + b + c
    | of_nat m , of_nat n , c => add_assoc_aux1 _ _ _
      |
        of_nat m , b , of_nat k
        =>
        by rw [ Int.add_comm , ← add_assoc_aux1 , Int.add_comm of_nat k , add_assoc_aux1 , Int.add_comm b ]
      |
        a , of_nat n , of_nat k
        =>
        by rw [ Int.add_comm , Int.add_comm a , ← add_assoc_aux1 , Int.add_comm a , Int.add_comm of_nat k ]
      | - [ 1 + m ] , - [ 1 + n ] , of_nat k => add_assoc_aux2 _ _ _
      |
        - [ 1 + m ] , of_nat n , - [ 1 + k ]
        =>
        by rw [ Int.add_comm , ← add_assoc_aux2 , Int.add_comm of_nat n , ← add_assoc_aux2 , Int.add_comm - [ 1 + m ] ]
      |
        of_nat m , - [ 1 + n ] , - [ 1 + k ]
        =>
        by
          rw
            [
              Int.add_comm , Int.add_comm of_nat m , Int.add_comm of_nat m , ← add_assoc_aux2 , Int.add_comm - [ 1 + k ]
              ]
      |
        - [ 1 + m ] , - [ 1 + n ] , - [ 1 + k ]
        =>
        by simp [ add_succ , Nat.add_comm , Nat.add_left_comm , neg_of_nat_of_succ ]

-- negation
theorem sub_nat_self : ∀ n, subNatNat n n = 0
  | 0 => rfl
  | succ m => by
    rw [sub_nat_nat_of_sub_eq_zero, Nat.sub_self, of_nat_zero]
    rw [Nat.sub_self]

attribute [local simp] sub_nat_self

protected theorem add_left_neg : ∀ a : ℤ, -a + a = 0
  | of_nat 0 => rfl
  | of_nat (succ m) => by simp
  | -[1 + m] => by simp

protected theorem add_right_neg (a : ℤ) : a + -a = 0 := by rw [Int.add_comm, Int.add_left_neg]

-- multiplication
protected theorem mul_comm : ∀ a b : ℤ, a * b = b * a
  | of_nat m, of_nat n => by simp [Nat.mul_comm]
  | of_nat m, -[1 + n] => by simp [Nat.mul_comm]
  | -[1 + m], of_nat n => by simp [Nat.mul_comm]
  | -[1 + m], -[1 + n] => by simp [Nat.mul_comm]

theorem of_nat_mul_neg_of_nat (m : ℕ) : ∀ n, ofNat m * negOfNat n = negOfNat (m * n)
  | 0 => rfl
  | succ n => by
    unfold neg_of_nat
    simp

theorem neg_of_nat_mul_of_nat (m n : ℕ) : negOfNat m * ofNat n = negOfNat (m * n) := by
  rw [Int.mul_comm]
  simp [of_nat_mul_neg_of_nat, Nat.mul_comm]

theorem neg_succ_of_nat_mul_neg_of_nat (m : ℕ) : ∀ n, -[1 + m] * negOfNat n = ofNat (succ m * n)
  | 0 => rfl
  | succ n => by
    unfold neg_of_nat
    simp

theorem neg_of_nat_mul_neg_succ_of_nat (m n : ℕ) : negOfNat n * -[1 + m] = ofNat (n * succ m) := by
  rw [Int.mul_comm]
  simp [neg_succ_of_nat_mul_neg_of_nat, Nat.mul_comm]

attribute [local simp]
  of_nat_mul_neg_of_nat neg_of_nat_mul_of_nat neg_succ_of_nat_mul_neg_of_nat neg_of_nat_mul_neg_succ_of_nat

protected theorem mul_assoc : ∀ a b c : ℤ, a * b * c = a * (b * c)
  | of_nat m, of_nat n, of_nat k => by simp [Nat.mul_assoc]
  | of_nat m, of_nat n, -[1 + k] => by simp [Nat.mul_assoc]
  | of_nat m, -[1 + n], of_nat k => by simp [Nat.mul_assoc]
  | of_nat m, -[1 + n], -[1 + k] => by simp [Nat.mul_assoc]
  | -[1 + m], of_nat n, of_nat k => by simp [Nat.mul_assoc]
  | -[1 + m], of_nat n, -[1 + k] => by simp [Nat.mul_assoc]
  | -[1 + m], -[1 + n], of_nat k => by simp [Nat.mul_assoc]
  | -[1 + m], -[1 + n], -[1 + k] => by simp [Nat.mul_assoc]

protected theorem mul_zero : ∀ a : ℤ, a * 0 = 0
  | of_nat m => rfl
  | -[1 + m] => rfl

protected theorem zero_mul (a : ℤ) : 0 * a = 0 :=
  Int.mul_comm a 0 ▸ Int.mul_zero a

theorem neg_of_nat_eq_sub_nat_nat_zero : ∀ n, negOfNat n = subNatNat 0 n
  | 0 => rfl
  | succ n => rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `of_nat_mul_sub_nat_nat [])
      (Command.declSig
       [(Term.explicitBinder "(" [`m `n `k] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_*_» (Term.app `ofNat [`m]) "*" (Term.app `subNatNat [`n `k]))
         "="
         (Term.app `subNatNat [(«term_*_» `m "*" `n) («term_*_» `m "*" `k)]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₀ []]
              [(Term.typeSpec ":" («term_∨_» («term_>_» `m ">" (num "0")) "∨" («term_=_» (num "0") "=" `m)))]
              ":="
              (Term.app `Decidable.lt_or_eq_of_le [`m.zero_le]))))
           []
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `h₀)]
            []
            ["with" [(Lean.binderIdent `h₀) (Lean.binderIdent `h₀)]])
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `Nat.lt_or_ge [`n `k]))))
              [])
             (group
              (Tactic.cases'
               "cases'"
               [(Tactic.casesTarget [] `h)]
               []
               ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
              [])
             (group
              («tactic___;_»
               (cdotTk (patternIgnore (token.«·» "·")))
               [(group
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h' []]
                    [(Term.typeSpec ":" («term_<_» («term_*_» `m "*" `n) "<" («term_*_» `m "*" `k)))]
                    ":="
                    (Term.app `Nat.mul_lt_mul_of_pos_left [`h `h₀]))))
                 [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h]))
                    ","
                    (Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h']))]
                   "]")
                  [])
                 [])
                (group (Tactic.simp "simp" [] [] [] [] []) [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h])]))]
                   "]")
                  [])
                 [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule ["←"] `neg_of_nat_of_succ) "," (Tactic.rwRule [] `Nat.mul_sub_left_distrib)]
                   "]")
                  [])
                 [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule ["←"] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])]))]
                   "]")
                  [])
                 [])
                (group (Tactic.tacticRfl "rfl") [])])
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h' []]
                 [(Term.typeSpec ":" («term_≤_» («term_*_» `m "*" `k) "≤" («term_*_» `m "*" `n)))]
                 ":="
                 (Term.app `Nat.mul_le_mul_left [(Term.hole "_") `h]))))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h]))
                 ","
                 (Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h']))]
                "]")
               [])
              [])
             (group (Tactic.simp "simp" [] [] [] [] []) [])
             (group
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.mul_sub_left_distrib)] "]") [])
              [])])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₂ []]
              [(Term.typeSpec ":" («term_=_» (Term.app `of_nat [(num "0")]) "=" (num "0")))]
              ":="
              `rfl)))
           []
           (Tactic.subst "subst" [`h₀])
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `h₂)
              ","
              (Tactic.simpLemma [] [] `Int.zero_mul)
              ","
              (Tactic.simpLemma [] [] `Nat.zero_mul)]
             "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₀ []]
             [(Term.typeSpec ":" («term_∨_» («term_>_» `m ">" (num "0")) "∨" («term_=_» (num "0") "=" `m)))]
             ":="
             (Term.app `Decidable.lt_or_eq_of_le [`m.zero_le]))))
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `h₀)]
           []
           ["with" [(Lean.binderIdent `h₀) (Lean.binderIdent `h₀)]])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `Nat.lt_or_ge [`n `k]))))
             [])
            (group
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] `h)]
              []
              ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
             [])
            (group
             («tactic___;_»
              (cdotTk (patternIgnore (token.«·» "·")))
              [(group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`h' []]
                   [(Term.typeSpec ":" («term_<_» («term_*_» `m "*" `n) "<" («term_*_» `m "*" `k)))]
                   ":="
                   (Term.app `Nat.mul_lt_mul_of_pos_left [`h `h₀]))))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h]))
                   ","
                   (Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h']))]
                  "]")
                 [])
                [])
               (group (Tactic.simp "simp" [] [] [] [] []) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h])]))]
                  "]")
                 [])
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] `neg_of_nat_of_succ) "," (Tactic.rwRule [] `Nat.mul_sub_left_distrib)]
                  "]")
                 [])
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])]))]
                  "]")
                 [])
                [])
               (group (Tactic.tacticRfl "rfl") [])])
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h' []]
                [(Term.typeSpec ":" («term_≤_» («term_*_» `m "*" `k) "≤" («term_*_» `m "*" `n)))]
                ":="
                (Term.app `Nat.mul_le_mul_left [(Term.hole "_") `h]))))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h]))
                ","
                (Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h']))]
               "]")
              [])
             [])
            (group (Tactic.simp "simp" [] [] [] [] []) [])
            (group
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.mul_sub_left_distrib)] "]") [])
             [])])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₂ []]
             [(Term.typeSpec ":" («term_=_» (Term.app `of_nat [(num "0")]) "=" (num "0")))]
             ":="
             `rfl)))
          []
          (Tactic.subst "subst" [`h₀])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `h₂)
             ","
             (Tactic.simpLemma [] [] `Int.zero_mul)
             ","
             (Tactic.simpLemma [] [] `Nat.zero_mul)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `h₂)
         ","
         (Tactic.simpLemma [] [] `Int.zero_mul)
         ","
         (Tactic.simpLemma [] [] `Nat.zero_mul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.zero_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.zero_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`h₀])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h₂ []]
         [(Term.typeSpec ":" («term_=_» (Term.app `of_nat [(num "0")]) "=" (num "0")))]
         ":="
         `rfl)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `of_nat [(num "0")]) "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `of_nat [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of_nat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `Nat.lt_or_ge [`n `k]))))
         [])
        (group
         (Tactic.cases' "cases'" [(Tactic.casesTarget [] `h)] [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
         [])
        (group
         («tactic___;_»
          (cdotTk (patternIgnore (token.«·» "·")))
          [(group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h' []]
               [(Term.typeSpec ":" («term_<_» («term_*_» `m "*" `n) "<" («term_*_» `m "*" `k)))]
               ":="
               (Term.app `Nat.mul_lt_mul_of_pos_left [`h `h₀]))))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h]))
               ","
               (Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h']))]
              "]")
             [])
            [])
           (group (Tactic.simp "simp" [] [] [] [] []) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h])]))]
              "]")
             [])
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `neg_of_nat_of_succ) "," (Tactic.rwRule [] `Nat.mul_sub_left_distrib)]
              "]")
             [])
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])]))]
              "]")
             [])
            [])
           (group (Tactic.tacticRfl "rfl") [])])
         [])
        (group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`h' []]
            [(Term.typeSpec ":" («term_≤_» («term_*_» `m "*" `k) "≤" («term_*_» `m "*" `n)))]
            ":="
            (Term.app `Nat.mul_le_mul_left [(Term.hole "_") `h]))))
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h]))
            ","
            (Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h']))]
           "]")
          [])
         [])
        (group (Tactic.simp "simp" [] [] [] [] []) [])
        (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.mul_sub_left_distrib)] "]") []) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.mul_sub_left_distrib)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.mul_sub_left_distrib
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h]))
         ","
         (Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h']))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sub_nat_nat_of_le [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sub_nat_nat_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sub_nat_nat_of_le [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sub_nat_nat_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h' []]
         [(Term.typeSpec ":" («term_≤_» («term_*_» `m "*" `k) "≤" («term_*_» `m "*" `n)))]
         ":="
         (Term.app `Nat.mul_le_mul_left [(Term.hole "_") `h]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.mul_le_mul_left [(Term.hole "_") `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.mul_le_mul_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» («term_*_» `m "*" `k) "≤" («term_*_» `m "*" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `m "*" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_» `m "*" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`h' []]
            [(Term.typeSpec ":" («term_<_» («term_*_» `m "*" `n) "<" («term_*_» `m "*" `k)))]
            ":="
            (Term.app `Nat.mul_lt_mul_of_pos_left [`h `h₀]))))
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h]))
            ","
            (Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h']))]
           "]")
          [])
         [])
        (group (Tactic.simp "simp" [] [] [] [] []) [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h])]))]
           "]")
          [])
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule ["←"] `neg_of_nat_of_succ) "," (Tactic.rwRule [] `Nat.mul_sub_left_distrib)]
           "]")
          [])
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule ["←"] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])]))]
           "]")
          [])
         [])
        (group (Tactic.tacticRfl "rfl") [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.sub_pos_of_lt [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.sub_pos_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Nat.sub_pos_of_lt [`h']) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `succ_pred_eq_of_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  of_nat_mul_sub_nat_nat
  ( m n k : ℕ ) : ofNat m * subNatNat n k = subNatNat m * n m * k
  :=
    by
      have h₀ : m > 0 ∨ 0 = m := Decidable.lt_or_eq_of_le m.zero_le
        cases' h₀ with h₀ h₀
        ·
          have h := Nat.lt_or_ge n k
            cases' h with h h
            ·
              have h' : m * n < m * k := Nat.mul_lt_mul_of_pos_left h h₀
                rw [ sub_nat_nat_of_lt h , sub_nat_nat_of_lt h' ]
                simp
                rw [ succ_pred_eq_of_pos Nat.sub_pos_of_lt h ]
                rw [ ← neg_of_nat_of_succ , Nat.mul_sub_left_distrib ]
                rw [ ← succ_pred_eq_of_pos Nat.sub_pos_of_lt h' ]
                rfl
            have h' : m * k ≤ m * n := Nat.mul_le_mul_left _ h
            rw [ sub_nat_nat_of_le h , sub_nat_nat_of_le h' ]
            simp
            rw [ Nat.mul_sub_left_distrib ]
        have h₂ : of_nat 0 = 0 := rfl
        subst h₀
        simp [ h₂ , Int.zero_mul , Nat.zero_mul ]

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

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_succ_of_nat_mul_sub_nat_nat [])
      (Command.declSig
       [(Term.explicitBinder "(" [`m `n `k] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_*_» («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]")) "*" (Term.app `subNatNat [`n `k]))
         "="
         (Term.app `subNatNat [(«term_*_» (Term.app `succ [`m]) "*" `k) («term_*_» (Term.app `succ [`m]) "*" `n)]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `Nat.lt_or_ge [`n `k]))))
           []
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `h)]
            []
            ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h' []]
                 [(Term.typeSpec
                   ":"
                   («term_<_» («term_*_» (Term.app `succ [`m]) "*" `n) "<" («term_*_» (Term.app `succ [`m]) "*" `k)))]
                 ":="
                 (Term.app `Nat.mul_lt_mul_of_pos_left [`h (Term.app `Nat.succ_pos [`m])]))))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h]))
                 ","
                 (Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [(Term.app `le_of_lt [`h'])]))]
                "]")
               [])
              [])
             (group
              (Tactic.simp
               "simp"
               []
               []
               []
               ["["
                [(Tactic.simpLemma [] [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h])]))
                 ","
                 (Tactic.simpLemma [] [] `Nat.mul_sub_left_distrib)]
                "]"]
               [])
              [])])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h' []]
              [(Term.typeSpec ":" («term_∨_» («term_>_» `n ">" `k) "∨" («term_=_» `k "=" `n)))]
              ":="
              (Term.app `Decidable.lt_or_eq_of_le [`h]))))
           []
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `h')]
            []
            ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h₁ []]
                 [(Term.typeSpec
                   ":"
                   («term_>_» («term_*_» (Term.app `succ [`m]) "*" `n) ">" («term_*_» (Term.app `succ [`m]) "*" `k)))]
                 ":="
                 (Term.app `Nat.mul_lt_mul_of_pos_left [`h' (Term.app `Nat.succ_pos [`m])]))))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h]))
                 ","
                 (Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h₁]))]
                "]")
               [])
              [])
             (group
              (Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpLemma [] [] `Nat.mul_sub_left_distrib) "," (Tactic.simpLemma [] [] `Nat.mul_comm)] "]"]
               [])
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `Nat.mul_comm [`k]))
                 ","
                 (Tactic.rwRule [] (Term.app `Nat.mul_comm [`n]))
                 ","
                 (Tactic.rwRule ["←"] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h₁])]))
                 ","
                 (Tactic.rwRule ["←"] `neg_of_nat_of_succ)]
                "]")
               [])
              [])
             (group (Tactic.tacticRfl "rfl") [])])
           []
           (Tactic.subst "subst" [`h'])
           []
           (Tactic.simp "simp" [] [] [] [] [])
           []
           (Tactic.tacticRfl "rfl")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `Nat.lt_or_ge [`n `k]))))
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `h)]
           []
           ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h' []]
                [(Term.typeSpec
                  ":"
                  («term_<_» («term_*_» (Term.app `succ [`m]) "*" `n) "<" («term_*_» (Term.app `succ [`m]) "*" `k)))]
                ":="
                (Term.app `Nat.mul_lt_mul_of_pos_left [`h (Term.app `Nat.succ_pos [`m])]))))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h]))
                ","
                (Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [(Term.app `le_of_lt [`h'])]))]
               "]")
              [])
             [])
            (group
             (Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h])]))
                ","
                (Tactic.simpLemma [] [] `Nat.mul_sub_left_distrib)]
               "]"]
              [])
             [])])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h' []]
             [(Term.typeSpec ":" («term_∨_» («term_>_» `n ">" `k) "∨" («term_=_» `k "=" `n)))]
             ":="
             (Term.app `Decidable.lt_or_eq_of_le [`h]))))
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `h')]
           []
           ["with" [(Lean.binderIdent `h') (Lean.binderIdent `h')]])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h₁ []]
                [(Term.typeSpec
                  ":"
                  («term_>_» («term_*_» (Term.app `succ [`m]) "*" `n) ">" («term_*_» (Term.app `succ [`m]) "*" `k)))]
                ":="
                (Term.app `Nat.mul_lt_mul_of_pos_left [`h' (Term.app `Nat.succ_pos [`m])]))))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h]))
                ","
                (Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h₁]))]
               "]")
              [])
             [])
            (group
             (Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] `Nat.mul_sub_left_distrib) "," (Tactic.simpLemma [] [] `Nat.mul_comm)] "]"]
              [])
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `Nat.mul_comm [`k]))
                ","
                (Tactic.rwRule [] (Term.app `Nat.mul_comm [`n]))
                ","
                (Tactic.rwRule ["←"] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h₁])]))
                ","
                (Tactic.rwRule ["←"] `neg_of_nat_of_succ)]
               "]")
              [])
             [])
            (group (Tactic.tacticRfl "rfl") [])])
          []
          (Tactic.subst "subst" [`h'])
          []
          (Tactic.simp "simp" [] [] [] [] [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`h'])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`h₁ []]
            [(Term.typeSpec
              ":"
              («term_>_» («term_*_» (Term.app `succ [`m]) "*" `n) ">" («term_*_» (Term.app `succ [`m]) "*" `k)))]
            ":="
            (Term.app `Nat.mul_lt_mul_of_pos_left [`h' (Term.app `Nat.succ_pos [`m])]))))
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] (Term.app `sub_nat_nat_of_le [`h]))
            ","
            (Tactic.rwRule [] (Term.app `sub_nat_nat_of_lt [`h₁]))]
           "]")
          [])
         [])
        (group
         (Tactic.simp
          "simp"
          []
          []
          []
          ["[" [(Tactic.simpLemma [] [] `Nat.mul_sub_left_distrib) "," (Tactic.simpLemma [] [] `Nat.mul_comm)] "]"]
          [])
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] (Term.app `Nat.mul_comm [`k]))
            ","
            (Tactic.rwRule [] (Term.app `Nat.mul_comm [`n]))
            ","
            (Tactic.rwRule ["←"] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h₁])]))
            ","
            (Tactic.rwRule ["←"] `neg_of_nat_of_succ)]
           "]")
          [])
         [])
        (group (Tactic.tacticRfl "rfl") [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `Nat.mul_comm [`k]))
         ","
         (Tactic.rwRule [] (Term.app `Nat.mul_comm [`n]))
         ","
         (Tactic.rwRule ["←"] (Term.app `succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`h₁])]))
         ","
         (Tactic.rwRule ["←"] `neg_of_nat_of_succ)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_of_nat_of_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  neg_succ_of_nat_mul_sub_nat_nat
  ( m n k : ℕ ) : - [ 1 + m ] * subNatNat n k = subNatNat succ m * k succ m * n
  :=
    by
      have h := Nat.lt_or_ge n k
        cases' h with h h
        ·
          have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h Nat.succ_pos m
            rw [ sub_nat_nat_of_lt h , sub_nat_nat_of_le le_of_lt h' ]
            simp [ succ_pred_eq_of_pos Nat.sub_pos_of_lt h , Nat.mul_sub_left_distrib ]
        have h' : n > k ∨ k = n := Decidable.lt_or_eq_of_le h
        cases' h' with h' h'
        ·
          have h₁ : succ m * n > succ m * k := Nat.mul_lt_mul_of_pos_left h' Nat.succ_pos m
            rw [ sub_nat_nat_of_le h , sub_nat_nat_of_lt h₁ ]
            simp [ Nat.mul_sub_left_distrib , Nat.mul_comm ]
            rw [ Nat.mul_comm k , Nat.mul_comm n , ← succ_pred_eq_of_pos Nat.sub_pos_of_lt h₁ , ← neg_of_nat_of_succ ]
            rfl
        subst h'
        simp
        rfl

attribute [local simp] of_nat_mul_sub_nat_nat neg_of_nat_add neg_succ_of_nat_mul_sub_nat_nat

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `distrib_left [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`a `b `c]
         [(Term.typeSpec ":" (Int.termℤ "ℤ"))]
         ","
         («term_=_»
          («term_*_» `a "*" («term_+_» `b "+" `c))
          "="
          («term_+_» («term_*_» `a "*" `b) "+" («term_*_» `a "*" `c))))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.app `of_nat [`m]) "," (Term.app `of_nat [`n]) "," (Term.app `of_nat [`k])]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Nat.left_distrib)] "]"] [])]))))
          (Term.matchAlt
           "|"
           [[(Term.app `of_nat [`m])
             ","
             (Term.app `of_nat [`n])
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `neg_of_nat_eq_sub_nat_nat_zero)] "]"] [])
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `sub_nat_nat_add)] "]") [])
               []
               (Tactic.tacticRfl "rfl")]))))
          (Term.matchAlt
           "|"
           [[(Term.app `of_nat [`m])
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `n)] "]"))
             ","
             (Term.app `of_nat [`k])]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `neg_of_nat_eq_sub_nat_nat_zero)] "]"] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Int.add_comm) "," (Tactic.rwRule ["←"] `sub_nat_nat_add)] "]")
                [])
               []
               (Tactic.tacticRfl "rfl")]))))
          (Term.matchAlt
           "|"
           [[(Term.app `of_nat [`m])
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `n)] "]"))
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] [] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `Nat.left_distrib)
                  ","
                  (Tactic.rwRule [] `add_succ)
                  ","
                  (Tactic.rwRule [] `succ_add)]
                 "]")
                [])]))))
          (Term.matchAlt
           "|"
           [[(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]"))
             ","
             (Term.app `of_nat [`n])
             ","
             (Term.app `of_nat [`k])]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Nat.mul_comm)] "]"] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `Nat.right_distrib) "," (Tactic.rwRule [] `Nat.mul_comm)]
                 "]")
                [])]))))
          (Term.matchAlt
           "|"
           [[(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]"))
             ","
             (Term.app `of_nat [`n])
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `neg_of_nat_eq_sub_nat_nat_zero)] "]"] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Int.add_comm) "," (Tactic.rwRule ["←"] `sub_nat_nat_add)] "]")
                [])
               []
               (Tactic.tacticRfl "rfl")]))))
          (Term.matchAlt
           "|"
           [[(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]"))
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `n)] "]"))
             ","
             (Term.app `of_nat [`k])]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `neg_of_nat_eq_sub_nat_nat_zero)] "]"] [])
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `sub_nat_nat_add)] "]") [])
               []
               (Tactic.tacticRfl "rfl")]))))
          (Term.matchAlt
           "|"
           [[(«term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `m)] "]"))
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `n)] "]"))
             ","
             («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `k)] "]"))]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] [] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `Nat.left_distrib)
                  ","
                  (Tactic.rwRule [] `add_succ)
                  ","
                  (Tactic.rwRule [] `succ_add)]
                 "]")
                [])]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] [] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `Nat.left_distrib) "," (Tactic.rwRule [] `add_succ) "," (Tactic.rwRule [] `succ_add)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `Nat.left_distrib) "," (Tactic.rwRule [] `add_succ) "," (Tactic.rwRule [] `succ_add)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `succ_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.left_distrib
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    distrib_left
    : ∀ a b c : ℤ , a * b + c = a * b + a * c
    | of_nat m , of_nat n , of_nat k => by simp [ Nat.left_distrib ]
      | of_nat m , of_nat n , - [ 1 + k ] => by simp [ neg_of_nat_eq_sub_nat_nat_zero ] rw [ ← sub_nat_nat_add ] rfl
      |
        of_nat m , - [ 1 + n ] , of_nat k
        =>
        by simp [ neg_of_nat_eq_sub_nat_nat_zero ] rw [ Int.add_comm , ← sub_nat_nat_add ] rfl
      | of_nat m , - [ 1 + n ] , - [ 1 + k ] => by simp rw [ ← Nat.left_distrib , add_succ , succ_add ]
      | - [ 1 + m ] , of_nat n , of_nat k => by simp [ Nat.mul_comm ] rw [ ← Nat.right_distrib , Nat.mul_comm ]
      |
        - [ 1 + m ] , of_nat n , - [ 1 + k ]
        =>
        by simp [ neg_of_nat_eq_sub_nat_nat_zero ] rw [ Int.add_comm , ← sub_nat_nat_add ] rfl
      | - [ 1 + m ] , - [ 1 + n ] , of_nat k => by simp [ neg_of_nat_eq_sub_nat_nat_zero ] rw [ ← sub_nat_nat_add ] rfl
      | - [ 1 + m ] , - [ 1 + n ] , - [ 1 + k ] => by simp rw [ ← Nat.left_distrib , add_succ , succ_add ]

protected theorem distrib_right (a b c : ℤ) : (a + b) * c = a * c + b * c := by
  rw [Int.mul_comm, Int.distrib_left]
  simp [Int.mul_comm]

protected theorem zero_ne_one : (0 : Int) ≠ 1 := fun h : 0 = 1 => succ_ne_zero _ (Int.ofNat.inj h).symm

theorem of_nat_sub {n m : ℕ} (h : m ≤ n) : ofNat (n - m) = ofNat n - ofNat m :=
  show ofNat (n - m) = ofNat n + negOfNat m from
    match m, h with
    | 0, h => rfl
    | succ m, h =>
      show ofNat (n - succ m) = subNatNat n (succ m) by delta sub_nat_nat <;> rw [Nat.sub_eq_zero_of_le h] <;> rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_left_comm [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b `c] [":" (Int.termℤ "ℤ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_» («term_+_» `a "+" («term_+_» `b "+" `c)) "=" («term_+_» `b "+" («term_+_» `a "+" `c)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule ["←"] `Int.add_assoc)
              ","
              (Tactic.rwRule [] (Term.app `Int.add_comm [`a]))
              ","
              (Tactic.rwRule [] `Int.add_assoc)]
             "]")
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `Int.add_assoc)
             ","
             (Tactic.rwRule [] (Term.app `Int.add_comm [`a]))
             ","
             (Tactic.rwRule [] `Int.add_assoc)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `Int.add_assoc)
         ","
         (Tactic.rwRule [] (Term.app `Int.add_comm [`a]))
         ","
         (Tactic.rwRule [] `Int.add_assoc)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.add_comm [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    add_left_comm
    ( a b c : ℤ ) : a + b + c = b + a + c
    := by rw [ ← Int.add_assoc , Int.add_comm a , Int.add_assoc ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_left_cancel [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b `c] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_=_» («term_+_» `a "+" `b) "=" («term_+_» `a "+" `c))] [] ")")]
       (Term.typeSpec ":" («term_=_» `b "=" `c)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_+_» («term-_» "-" `a) "+" («term_+_» `a "+" `b))
                 "="
                 («term_+_» («term-_» "-" `a) "+" («term_+_» `a "+" `c))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])]))))))
           []
           (tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule ["←"] `Int.add_assoc)
              ","
              (Tactic.rwRule ["←"] `Int.add_assoc)
              ","
              (Tactic.rwRule [] `Int.add_left_neg)
              ","
              (Tactic.rwRule [] `Int.zero_add)
              ","
              (Tactic.rwRule [] `Int.zero_add)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_+_» («term-_» "-" `a) "+" («term_+_» `a "+" `b))
                "="
                («term_+_» («term-_» "-" `a) "+" («term_+_» `a "+" `c))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])]))))))
          []
          (tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `Int.add_assoc)
             ","
             (Tactic.rwRule ["←"] `Int.add_assoc)
             ","
             (Tactic.rwRule [] `Int.add_left_neg)
             ","
             (Tactic.rwRule [] `Int.zero_add)
             ","
             (Tactic.rwRule [] `Int.zero_add)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `Int.add_assoc)
         ","
         (Tactic.rwRule ["←"] `Int.add_assoc)
         ","
         (Tactic.rwRule [] `Int.add_left_neg)
         ","
         (Tactic.rwRule [] `Int.zero_add)
         ","
         (Tactic.rwRule [] `Int.zero_add)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_left_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    add_left_cancel
    { a b c : ℤ } ( h : a + b = a + c ) : b = c
    :=
      by
        have : - a + a + b = - a + a + c := by rw [ h ]
          rwa [ ← Int.add_assoc , ← Int.add_assoc , Int.add_left_neg , Int.zero_add , Int.zero_add ] at this

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_add [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Int.termℤ "ℤ")] "}")]
       (Term.typeSpec
        ":"
        («term_=_» («term-_» "-" («term_+_» `a "+" `b)) "=" («term_+_» («term-_» "-" `a) "+" («term-_» "-" `b)))))
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         («term_=_»
          («term-_» "-" («term_+_» `a "+" `b))
          "="
          («term_+_»
           («term_+_» («term_+_» («term-_» "-" («term_+_» `a "+" `b)) "+" («term_+_» `a "+" `b)) "+" («term-_» "-" `a))
           "+"
           («term-_» "-" `b)))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Int.add_assoc)
                ","
                (Tactic.rwRule [] (Term.app `Int.add_comm [(«term-_» "-" `a)]))
                ","
                (Tactic.rwRule [] `Int.add_assoc)
                ","
                (Tactic.rwRule [] `Int.add_assoc)
                ","
                (Tactic.rwRule ["←"] (Term.app `Int.add_assoc [`b]))]
               "]")
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Int.add_right_neg)
                ","
                (Tactic.rwRule [] `Int.zero_add)
                ","
                (Tactic.rwRule [] `Int.add_right_neg)
                ","
                (Tactic.rwRule [] `Int.add_zero)]
               "]")
              [])]))))
        [(calcStep
          («term_=_» (Term.hole "_") "=" («term_+_» («term-_» "-" `a) "+" («term-_» "-" `b)))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Int.add_left_neg) "," (Tactic.rwRule [] `Int.zero_add)] "]")
               [])]))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        («term_=_»
         («term-_» "-" («term_+_» `a "+" `b))
         "="
         («term_+_»
          («term_+_» («term_+_» («term-_» "-" («term_+_» `a "+" `b)) "+" («term_+_» `a "+" `b)) "+" («term-_» "-" `a))
          "+"
          («term-_» "-" `b)))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Int.add_assoc)
               ","
               (Tactic.rwRule [] (Term.app `Int.add_comm [(«term-_» "-" `a)]))
               ","
               (Tactic.rwRule [] `Int.add_assoc)
               ","
               (Tactic.rwRule [] `Int.add_assoc)
               ","
               (Tactic.rwRule ["←"] (Term.app `Int.add_assoc [`b]))]
              "]")
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Int.add_right_neg)
               ","
               (Tactic.rwRule [] `Int.zero_add)
               ","
               (Tactic.rwRule [] `Int.add_right_neg)
               ","
               (Tactic.rwRule [] `Int.add_zero)]
              "]")
             [])]))))
       [(calcStep
         («term_=_» (Term.hole "_") "=" («term_+_» («term-_» "-" `a) "+" («term-_» "-" `b)))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Int.add_left_neg) "," (Tactic.rwRule [] `Int.zero_add)] "]")
              [])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Int.add_left_neg) "," (Tactic.rwRule [] `Int.zero_add)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Int.add_left_neg) "," (Tactic.rwRule [] `Int.zero_add)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_left_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" («term_+_» («term-_» "-" `a) "+" («term-_» "-" `b)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» («term-_» "-" `a) "+" («term-_» "-" `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 66 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term-_» "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 100, (some 100, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Int.add_assoc)
             ","
             (Tactic.rwRule [] (Term.app `Int.add_comm [(«term-_» "-" `a)]))
             ","
             (Tactic.rwRule [] `Int.add_assoc)
             ","
             (Tactic.rwRule [] `Int.add_assoc)
             ","
             (Tactic.rwRule ["←"] (Term.app `Int.add_assoc [`b]))]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Int.add_right_neg)
             ","
             (Tactic.rwRule [] `Int.zero_add)
             ","
             (Tactic.rwRule [] `Int.add_right_neg)
             ","
             (Tactic.rwRule [] `Int.add_zero)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Int.add_right_neg)
         ","
         (Tactic.rwRule [] `Int.zero_add)
         ","
         (Tactic.rwRule [] `Int.add_right_neg)
         ","
         (Tactic.rwRule [] `Int.add_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_right_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_right_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Int.add_assoc)
         ","
         (Tactic.rwRule [] (Term.app `Int.add_comm [(«term-_» "-" `a)]))
         ","
         (Tactic.rwRule [] `Int.add_assoc)
         ","
         (Tactic.rwRule [] `Int.add_assoc)
         ","
         (Tactic.rwRule ["←"] (Term.app `Int.add_assoc [`b]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.add_assoc [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.add_assoc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    neg_add
    { a b : ℤ } : - a + b = - a + - b
    :=
      calc
        - a + b = - a + b + a + b + - a + - b
          :=
          by
            rw [ Int.add_assoc , Int.add_comm - a , Int.add_assoc , Int.add_assoc , ← Int.add_assoc b ]
              rw [ Int.add_right_neg , Int.zero_add , Int.add_right_neg , Int.add_zero ]
        _ = - a + - b := by rw [ Int.add_left_neg , Int.zero_add ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_succ_of_nat_coe' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term-_» "-" («term[_]» "[" [(«term_+_» (num "1") "+" `n)] "]"))
         "="
         («term_-_» («term-_» "-" (coeNotation "↑" `n)) "-" (num "1")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Int.sub_eq_add_neg) "," (Tactic.rwRule ["←"] `Int.neg_add)] "]")
             [])
            "<;>"
            (Tactic.tacticRfl "rfl"))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Int.sub_eq_add_neg) "," (Tactic.rwRule ["←"] `Int.neg_add)] "]")
            [])
           "<;>"
           (Tactic.tacticRfl "rfl"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Int.sub_eq_add_neg) "," (Tactic.rwRule ["←"] `Int.neg_add)] "]")
        [])
       "<;>"
       (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Int.sub_eq_add_neg) "," (Tactic.rwRule ["←"] `Int.neg_add)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.neg_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem neg_succ_of_nat_coe' ( n : ℕ ) : - [ 1 + n ] = - ↑ n - 1 := by rw [ Int.sub_eq_add_neg , ← Int.neg_add ] <;> rfl

protected theorem coe_nat_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n :=
  of_nat_sub

attribute [local simp] Int.sub_eq_add_neg

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `sub_nat_nat_eq_coe [])
      (Command.declSig
       [(Term.implicitBinder "{" [`m `n] [":" (termℕ "ℕ")] "}")]
       (Term.typeSpec
        ":"
        («term_=_» (Term.app `subNatNat [`m `n]) "=" («term_-_» (coeNotation "↑" `m) "-" (coeNotation "↑" `n)))))
      (Command.declValSimple
       ":="
       (Term.app
        `sub_nat_nat_elim
        [`m
         `n
         (Term.fun
          "fun"
          (Term.basicFun
           [`m `n `i]
           []
           "=>"
           («term_=_» `i "=" («term_-_» (coeNotation "↑" `m) "-" (coeNotation "↑" `n)))))
         (Term.fun
          "fun"
          (Term.basicFun
           [`i `n]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] `Int.coe_nat_add)
                  ","
                  (Tactic.simpLemma [] [] `Int.add_left_comm)
                  ","
                  (Tactic.simpLemma [] [] `Int.add_assoc)
                  ","
                  (Tactic.simpLemma [] [] `Int.add_right_neg)]
                 "]"]
                [])
               []
               (Tactic.tacticRfl "rfl")])))))
         (Term.fun
          "fun"
          (Term.basicFun
           [`i `n]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Int.coe_nat_add)
                  ","
                  (Tactic.rwRule [] `Int.coe_nat_add)
                  ","
                  (Tactic.rwRule [] `Int.coe_nat_one)
                  ","
                  (Tactic.rwRule [] `Int.neg_succ_of_nat_eq)
                  ","
                  (Tactic.rwRule [] `Int.sub_eq_add_neg)
                  ","
                  (Tactic.rwRule [] `Int.neg_add)
                  ","
                  (Tactic.rwRule [] `Int.neg_add)
                  ","
                  (Tactic.rwRule [] `Int.neg_add)
                  ","
                  (Tactic.rwRule ["←"] `Int.add_assoc)
                  ","
                  (Tactic.rwRule ["←"] `Int.add_assoc)
                  ","
                  (Tactic.rwRule [] `Int.add_right_neg)
                  ","
                  (Tactic.rwRule [] `Int.zero_add)]
                 "]")
                [])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sub_nat_nat_elim
       [`m
        `n
        (Term.fun
         "fun"
         (Term.basicFun
          [`m `n `i]
          []
          "=>"
          («term_=_» `i "=" («term_-_» (coeNotation "↑" `m) "-" (coeNotation "↑" `n)))))
        (Term.fun
         "fun"
         (Term.basicFun
          [`i `n]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               []
               ["["
                [(Tactic.simpLemma [] [] `Int.coe_nat_add)
                 ","
                 (Tactic.simpLemma [] [] `Int.add_left_comm)
                 ","
                 (Tactic.simpLemma [] [] `Int.add_assoc)
                 ","
                 (Tactic.simpLemma [] [] `Int.add_right_neg)]
                "]"]
               [])
              []
              (Tactic.tacticRfl "rfl")])))))
        (Term.fun
         "fun"
         (Term.basicFun
          [`i `n]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Int.coe_nat_add)
                 ","
                 (Tactic.rwRule [] `Int.coe_nat_add)
                 ","
                 (Tactic.rwRule [] `Int.coe_nat_one)
                 ","
                 (Tactic.rwRule [] `Int.neg_succ_of_nat_eq)
                 ","
                 (Tactic.rwRule [] `Int.sub_eq_add_neg)
                 ","
                 (Tactic.rwRule [] `Int.neg_add)
                 ","
                 (Tactic.rwRule [] `Int.neg_add)
                 ","
                 (Tactic.rwRule [] `Int.neg_add)
                 ","
                 (Tactic.rwRule ["←"] `Int.add_assoc)
                 ","
                 (Tactic.rwRule ["←"] `Int.add_assoc)
                 ","
                 (Tactic.rwRule [] `Int.add_right_neg)
                 ","
                 (Tactic.rwRule [] `Int.zero_add)]
                "]")
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i `n]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Int.coe_nat_add)
               ","
               (Tactic.rwRule [] `Int.coe_nat_add)
               ","
               (Tactic.rwRule [] `Int.coe_nat_one)
               ","
               (Tactic.rwRule [] `Int.neg_succ_of_nat_eq)
               ","
               (Tactic.rwRule [] `Int.sub_eq_add_neg)
               ","
               (Tactic.rwRule [] `Int.neg_add)
               ","
               (Tactic.rwRule [] `Int.neg_add)
               ","
               (Tactic.rwRule [] `Int.neg_add)
               ","
               (Tactic.rwRule ["←"] `Int.add_assoc)
               ","
               (Tactic.rwRule ["←"] `Int.add_assoc)
               ","
               (Tactic.rwRule [] `Int.add_right_neg)
               ","
               (Tactic.rwRule [] `Int.zero_add)]
              "]")
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Int.coe_nat_add)
             ","
             (Tactic.rwRule [] `Int.coe_nat_add)
             ","
             (Tactic.rwRule [] `Int.coe_nat_one)
             ","
             (Tactic.rwRule [] `Int.neg_succ_of_nat_eq)
             ","
             (Tactic.rwRule [] `Int.sub_eq_add_neg)
             ","
             (Tactic.rwRule [] `Int.neg_add)
             ","
             (Tactic.rwRule [] `Int.neg_add)
             ","
             (Tactic.rwRule [] `Int.neg_add)
             ","
             (Tactic.rwRule ["←"] `Int.add_assoc)
             ","
             (Tactic.rwRule ["←"] `Int.add_assoc)
             ","
             (Tactic.rwRule [] `Int.add_right_neg)
             ","
             (Tactic.rwRule [] `Int.zero_add)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Int.coe_nat_add)
         ","
         (Tactic.rwRule [] `Int.coe_nat_add)
         ","
         (Tactic.rwRule [] `Int.coe_nat_one)
         ","
         (Tactic.rwRule [] `Int.neg_succ_of_nat_eq)
         ","
         (Tactic.rwRule [] `Int.sub_eq_add_neg)
         ","
         (Tactic.rwRule [] `Int.neg_add)
         ","
         (Tactic.rwRule [] `Int.neg_add)
         ","
         (Tactic.rwRule [] `Int.neg_add)
         ","
         (Tactic.rwRule ["←"] `Int.add_assoc)
         ","
         (Tactic.rwRule ["←"] `Int.add_assoc)
         ","
         (Tactic.rwRule [] `Int.add_right_neg)
         ","
         (Tactic.rwRule [] `Int.zero_add)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_right_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    sub_nat_nat_eq_coe
    { m n : ℕ } : subNatNat m n = ↑ m - ↑ n
    :=
      sub_nat_nat_elim
        m
          n
          fun m n i => i = ↑ m - ↑ n
          fun i n => by simp [ Int.coe_nat_add , Int.add_left_comm , Int.add_assoc , Int.add_right_neg ] rfl
          fun
            i n
              =>
              by
                rw
                  [
                    Int.coe_nat_add
                      ,
                      Int.coe_nat_add
                      ,
                      Int.coe_nat_one
                      ,
                      Int.neg_succ_of_nat_eq
                      ,
                      Int.sub_eq_add_neg
                      ,
                      Int.neg_add
                      ,
                      Int.neg_add
                      ,
                      Int.neg_add
                      ,
                      ← Int.add_assoc
                      ,
                      ← Int.add_assoc
                      ,
                      Int.add_right_neg
                      ,
                      Int.zero_add
                    ]

def toNat : ℤ → ℕ
  | (n : ℕ) => n
  | -[1 + n] => 0

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_nat_sub [])
      (Command.declSig
       [(Term.explicitBinder "(" [`m `n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec ":" («term_=_» (Term.app `toNat [(«term_-_» `m "-" `n)]) "=" («term_-_» `m "-" `n))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.sub_nat_nat_eq_coe)] "]") [])
            "<;>"
            (Tactic.exact
             "exact"
             (Term.app
              `sub_nat_nat_elim
              [`m
               `n
               (Term.fun
                "fun"
                (Term.basicFun [`m `n `i] [] "=>" («term_=_» (Term.app `to_nat [`i]) "=" («term_-_» `m "-" `n))))
               (Term.fun
                "fun"
                (Term.basicFun
                 [`i `n]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_sub_cancel_left)] "]") [])
                      "<;>"
                      (Tactic.tacticRfl "rfl"))])))))
               (Term.fun
                "fun"
                (Term.basicFun
                 [`i `n]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [] `Nat.add_assoc)
                         ","
                         (Tactic.rwRule
                          []
                          (Term.app
                           `Nat.sub_eq_zero_of_le
                           [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))]
                        "]")
                       [])
                      "<;>"
                      (Tactic.tacticRfl "rfl"))])))))])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.sub_nat_nat_eq_coe)] "]") [])
           "<;>"
           (Tactic.exact
            "exact"
            (Term.app
             `sub_nat_nat_elim
             [`m
              `n
              (Term.fun
               "fun"
               (Term.basicFun [`m `n `i] [] "=>" («term_=_» (Term.app `to_nat [`i]) "=" («term_-_» `m "-" `n))))
              (Term.fun
               "fun"
               (Term.basicFun
                [`i `n]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_sub_cancel_left)] "]") [])
                     "<;>"
                     (Tactic.tacticRfl "rfl"))])))))
              (Term.fun
               "fun"
               (Term.basicFun
                [`i `n]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `Nat.add_assoc)
                        ","
                        (Tactic.rwRule
                         []
                         (Term.app
                          `Nat.sub_eq_zero_of_le
                          [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))]
                       "]")
                      [])
                     "<;>"
                     (Tactic.tacticRfl "rfl"))])))))])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.sub_nat_nat_eq_coe)] "]") [])
       "<;>"
       (Tactic.exact
        "exact"
        (Term.app
         `sub_nat_nat_elim
         [`m
          `n
          (Term.fun
           "fun"
           (Term.basicFun [`m `n `i] [] "=>" («term_=_» (Term.app `to_nat [`i]) "=" («term_-_» `m "-" `n))))
          (Term.fun
           "fun"
           (Term.basicFun
            [`i `n]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_sub_cancel_left)] "]") [])
                 "<;>"
                 (Tactic.tacticRfl "rfl"))])))))
          (Term.fun
           "fun"
           (Term.basicFun
            [`i `n]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Nat.add_assoc)
                    ","
                    (Tactic.rwRule
                     []
                     (Term.app
                      `Nat.sub_eq_zero_of_le
                      [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))]
                   "]")
                  [])
                 "<;>"
                 (Tactic.tacticRfl "rfl"))])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `sub_nat_nat_elim
        [`m
         `n
         (Term.fun
          "fun"
          (Term.basicFun [`m `n `i] [] "=>" («term_=_» (Term.app `to_nat [`i]) "=" («term_-_» `m "-" `n))))
         (Term.fun
          "fun"
          (Term.basicFun
           [`i `n]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_sub_cancel_left)] "]") [])
                "<;>"
                (Tactic.tacticRfl "rfl"))])))))
         (Term.fun
          "fun"
          (Term.basicFun
           [`i `n]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Nat.add_assoc)
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app `Nat.sub_eq_zero_of_le [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))]
                  "]")
                 [])
                "<;>"
                (Tactic.tacticRfl "rfl"))])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sub_nat_nat_elim
       [`m
        `n
        (Term.fun
         "fun"
         (Term.basicFun [`m `n `i] [] "=>" («term_=_» (Term.app `to_nat [`i]) "=" («term_-_» `m "-" `n))))
        (Term.fun
         "fun"
         (Term.basicFun
          [`i `n]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_sub_cancel_left)] "]") [])
               "<;>"
               (Tactic.tacticRfl "rfl"))])))))
        (Term.fun
         "fun"
         (Term.basicFun
          [`i `n]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Nat.add_assoc)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `Nat.sub_eq_zero_of_le [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))]
                 "]")
                [])
               "<;>"
               (Tactic.tacticRfl "rfl"))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i `n]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Nat.add_assoc)
                ","
                (Tactic.rwRule
                 []
                 (Term.app `Nat.sub_eq_zero_of_le [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))]
               "]")
              [])
             "<;>"
             (Tactic.tacticRfl "rfl"))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Nat.add_assoc)
              ","
              (Tactic.rwRule
               []
               (Term.app `Nat.sub_eq_zero_of_le [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))]
             "]")
            [])
           "<;>"
           (Tactic.tacticRfl "rfl"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Nat.add_assoc)
          ","
          (Tactic.rwRule
           []
           (Term.app `Nat.sub_eq_zero_of_le [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))]
         "]")
        [])
       "<;>"
       (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Nat.add_assoc)
         ","
         (Tactic.rwRule
          []
          (Term.app `Nat.sub_eq_zero_of_le [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.sub_eq_zero_of_le [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.le_add_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     [(Term.app `Nat.le_add_right [(Term.hole "_") (Term.hole "_")]) []]
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.sub_eq_zero_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i `n]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_sub_cancel_left)] "]") [])
             "<;>"
             (Tactic.tacticRfl "rfl"))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_sub_cancel_left)] "]") [])
           "<;>"
           (Tactic.tacticRfl "rfl"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_sub_cancel_left)] "]") [])
       "<;>"
       (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_sub_cancel_left)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.add_sub_cancel_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     [(Term.fun
       "fun"
       (Term.basicFun
        [`i `n]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.add_sub_cancel_left)] "]") [])
             "<;>"
             (Tactic.tacticRfl "rfl"))])))))
      []]
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`m `n `i] [] "=>" («term_=_» (Term.app `to_nat [`i]) "=" («term_-_» `m "-" `n))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `to_nat [`i]) "=" («term_-_» `m "-" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `m "-" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `to_nat [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_nat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     [(Term.fun "fun" (Term.basicFun [`m `n `i] [] "=>" («term_=_» (Term.app `to_nat [`i]) "=" («term_-_» `m "-" `n))))
      []]
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sub_nat_nat_elim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.sub_nat_nat_eq_coe)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.sub_nat_nat_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  to_nat_sub
  ( m n : ℕ ) : toNat m - n = m - n
  :=
    by
      rw [ ← Int.sub_nat_nat_eq_coe ]
        <;>
        exact
          sub_nat_nat_elim
            m
              n
              fun m n i => to_nat i = m - n
              fun i n => by rw [ Nat.add_sub_cancel_left ] <;> rfl
              fun i n => by rw [ Nat.add_assoc , Nat.sub_eq_zero_of_le Nat.le_add_right _ _ ] <;> rfl

-- Since mod x y is always nonnegative when y ≠ 0, we can make a nat version of it
def natMod (m n : ℤ) : ℕ :=
  (m % n).toNat

protected theorem one_mul : ∀ a : ℤ, (1 : ℤ) * a = a
  | of_nat n => show ofNat (1 * n) = ofNat n by rw [Nat.one_mul]
  | -[1 + n] => show -[1 + 1 * n] = -[1 + n] by rw [Nat.one_mul]

protected theorem mul_one (a : ℤ) : a * 1 = a := by rw [Int.mul_comm, Int.one_mul]

protected theorem neg_eq_neg_one_mul : ∀ a : ℤ, -a = -1 * a
  | of_nat 0 => rfl
  | of_nat (n + 1) =>
    show _ = -[1 + (1 * n + 0)] by
      rw [Nat.one_mul]
      rfl
  | -[1 + n] =>
    show _ = ofNat _ by
      rw [Nat.one_mul]
      rfl

theorem sign_mul_nat_abs : ∀ a : ℤ, sign a * natAbs a = a
  | (n + 1 : ℕ) => Int.one_mul _
  | 0 => rfl
  | -[1 + n] => (Int.neg_eq_neg_one_mul _).symm

end Int

