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
  have : -a = -0 := by rwa [Int.neg_zero]
  have : a = 0 := Int.neg_inj this
  contradiction

protected theorem zero_ne_neg_of_ne {a : ℤ} (h : 0 ≠ a) : 0 ≠ -a :=
  Ne.symm (Int.neg_ne_zero_of_ne (Ne.symm h))

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_ne_of_pos [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Int.termℤ "ℤ")] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         («term_<_» (num "0") "<" `a)
         "→"
         (Term.arrow («term_<_» (num "0") "<" `b) "→" («term_≠_» («term-_» "-" `a) "≠" `b)))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`h₁ `h₂ `h]
         []
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
             []
             (Tactic.change
              "change"
              («term_<_» (num "0") "<" `a)
              [(Tactic.location "at" (Tactic.locationHyp [`h₁] []))])
             []
             (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `le_of_lt [`h₁]))))
             []
             (Tactic.exact
              "exact"
              (Term.app
               `absurd
               [(Term.app `le_of_lt [`h₁]) (Term.app `not_le_of_gt [(Term.app `Int.neg_of_neg_pos [`h₂])])]))])))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h₁ `h₂ `h]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
            []
            (Tactic.change "change" («term_<_» (num "0") "<" `a) [(Tactic.location "at" (Tactic.locationHyp [`h₁] []))])
            []
            (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `le_of_lt [`h₁]))))
            []
            (Tactic.exact
             "exact"
             (Term.app
              `absurd
              [(Term.app `le_of_lt [`h₁]) (Term.app `not_le_of_gt [(Term.app `Int.neg_of_neg_pos [`h₂])])]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
          []
          (Tactic.change "change" («term_<_» (num "0") "<" `a) [(Tactic.location "at" (Tactic.locationHyp [`h₁] []))])
          []
          (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `le_of_lt [`h₁]))))
          []
          (Tactic.exact
           "exact"
           (Term.app
            `absurd
            [(Term.app `le_of_lt [`h₁]) (Term.app `not_le_of_gt [(Term.app `Int.neg_of_neg_pos [`h₂])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `absurd [(Term.app `le_of_lt [`h₁]) (Term.app `not_le_of_gt [(Term.app `Int.neg_of_neg_pos [`h₂])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `absurd [(Term.app `le_of_lt [`h₁]) (Term.app `not_le_of_gt [(Term.app `Int.neg_of_neg_pos [`h₂])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not_le_of_gt [(Term.app `Int.neg_of_neg_pos [`h₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.neg_of_neg_pos [`h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.neg_of_neg_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Int.neg_of_neg_pos [`h₂]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_le_of_gt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     [(Term.app `not_le_of_gt [(Term.paren "(" [(Term.app `Int.neg_of_neg_pos [`h₂]) []] ")")]) []]
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_of_lt [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_of_lt [`h₁]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `absurd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `le_of_lt [`h₁]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_lt [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change "change" («term_<_» (num "0") "<" `a) [(Tactic.location "at" (Tactic.locationHyp [`h₁] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (num "0") "<" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
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
    neg_ne_of_pos
    { a b : ℤ } : 0 < a → 0 < b → - a ≠ b
    :=
      fun
        h₁ h₂ h
          =>
          by
            rw [ ← h ] at h₂
              change 0 < a at h₁
              have := le_of_lt h₁
              exact absurd le_of_lt h₁ not_le_of_gt Int.neg_of_neg_pos h₂

protected theorem ne_neg_of_pos {a b : ℤ} : 0 < a → 0 < b → a ≠ -b := fun h₁ h₂ => Ne.symm (Int.neg_ne_of_pos h₂ h₁)

-- 2. Lemmas for proving that positive int numerals are nonneg and positive
protected theorem one_pos : 0 < (1 : Int) :=
  Int.zero_lt_one

protected theorem bit0_pos {a : ℤ} : 0 < a → 0 < bit0 a := fun h => Int.add_pos h h

protected theorem bit1_pos {a : ℤ} : 0 ≤ a → 0 < bit1 a := fun h =>
  Int.lt_add_of_le_of_pos (Int.add_nonneg h h) Int.zero_lt_one

protected theorem zero_nonneg : 0 ≤ (0 : ℤ) :=
  le_refl 0

protected theorem one_nonneg : 0 ≤ (1 : ℤ) :=
  le_of_lt Int.zero_lt_one

protected theorem bit0_nonneg {a : ℤ} : 0 ≤ a → 0 ≤ bit0 a := fun h => Int.add_nonneg h h

protected theorem bit1_nonneg {a : ℤ} : 0 ≤ a → 0 ≤ bit1 a := fun h => le_of_lt (Int.bit1_pos h)

protected theorem nonneg_of_pos {a : ℤ} : 0 < a → 0 ≤ a :=
  le_of_lt

-- 3. nat_abs auxiliary lemmas
theorem neg_succ_of_nat_lt_zero (n : ℕ) : negSucc n < 0 :=
  @lt.intro _ _ n
    (by
      simp [neg_succ_of_nat_coe, Int.coe_nat_succ, Int.coe_nat_add, Int.coe_nat_one, Int.add_comm, Int.add_left_comm,
        Int.neg_add, Int.add_right_neg, Int.zero_add])

theorem zero_le_of_nat (n : ℕ) : 0 ≤ ofNat n :=
  @le.intro _ _ n (by rw [Int.zero_add, Int.coe_nat_eq])

theorem of_nat_nat_abs_eq_of_nonneg : ∀ {a : ℤ}, 0 ≤ a → ofNat (natAbs a) = a
  | of_nat n, h => rfl
  | neg_succ_of_nat n, h => absurd (neg_succ_of_nat_lt_zero n) (not_lt_of_ge h)

theorem ne_of_nat_abs_ne_nat_abs_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : natAbs a ≠ natAbs b) : a ≠ b :=
  fun h => by
  have : ofNat (natAbs a) = ofNat (natAbs b) := by rwa [of_nat_nat_abs_eq_of_nonneg ha, of_nat_nat_abs_eq_of_nonneg hb]
  injection this
  contradiction

protected theorem ne_of_nat_ne_nonneg_case {a b : ℤ} {n m : Nat} (ha : 0 ≤ a) (hb : 0 ≤ b) (e1 : natAbs a = n)
    (e2 : natAbs b = m) (h : n ≠ m) : a ≠ b :=
  have : natAbs a ≠ natAbs b := by rwa [e1, e2]
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
    simp [nat_abs_of_nat_core, this]
  | _, neg_succ_of_nat m, h₁, h₂ => absurd (neg_succ_of_nat_lt_zero m) (not_lt_of_ge h₂)
  | neg_succ_of_nat n, _, h₁, h₂ => absurd (neg_succ_of_nat_lt_zero n) (not_lt_of_ge h₁)

protected theorem nat_abs_add_neg : ∀ {a b : Int}, a < 0 → b < 0 → natAbs (a + b) = natAbs a + natAbs b
  | neg_succ_of_nat n, neg_succ_of_nat m, h₁, h₂ => by
    have : -[1 + n] + -[1 + m] = -[1 + Nat.succ (n + m)] := rfl
    simp [nat_abs_of_neg_succ_of_nat, this, Nat.succ_add, Nat.add_succ]

protected theorem nat_abs_bit0 : ∀ a : Int, natAbs (bit0 a) = bit0 (natAbs a)
  | of_nat n => Int.nat_abs_add_nonneg (zero_le_of_nat n) (zero_le_of_nat n)
  | neg_succ_of_nat n => Int.nat_abs_add_neg (neg_succ_of_nat_lt_zero n) (neg_succ_of_nat_lt_zero n)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nat_abs_bit0_step [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `Int] "}")
        (Term.implicitBinder "{" [`n] [":" `Nat] "}")
        (Term.explicitBinder "(" [`h] [":" («term_=_» (Term.app `natAbs [`a]) "=" `n)] [] ")")]
       (Term.typeSpec ":" («term_=_» (Term.app `natAbs [(Term.app `bit0 [`a])]) "=" (Term.app `bit0 [`n]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]") [])
           []
           (Tactic.apply "apply" `Int.nat_abs_bit0)])))
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
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]") [])
          []
          (Tactic.apply "apply" `Int.nat_abs_bit0)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `Int.nat_abs_bit0)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.nat_abs_bit0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
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
    nat_abs_bit0_step
    { a : Int } { n : Nat } ( h : natAbs a = n ) : natAbs bit0 a = bit0 n
    := by rw [ ← h ] apply Int.nat_abs_bit0

protected theorem nat_abs_bit1_nonneg {a : Int} (h : 0 ≤ a) : natAbs (bit1 a) = bit1 (natAbs a) :=
  show natAbs (bit0 a + 1) = bit0 (natAbs a) + natAbs 1 by
    rw [Int.nat_abs_add_nonneg (Int.bit0_nonneg h) (le_of_lt Int.zero_lt_one), Int.nat_abs_bit0]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nat_abs_bit1_nonneg_step [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `Int] "}")
        (Term.implicitBinder "{" [`n] [":" `Nat] "}")
        (Term.explicitBinder "(" [`h₁] [":" («term_≤_» (num "0") "≤" `a)] [] ")")
        (Term.explicitBinder "(" [`h₂] [":" («term_=_» (Term.app `natAbs [`a]) "=" `n)] [] ")")]
       (Term.typeSpec ":" («term_=_» (Term.app `natAbs [(Term.app `bit1 [`a])]) "=" (Term.app `bit1 [`n]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h₂)] "]") [])
           []
           (Tactic.apply "apply" (Term.app `Int.nat_abs_bit1_nonneg [`h₁]))])))
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
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h₂)] "]") [])
          []
          (Tactic.apply "apply" (Term.app `Int.nat_abs_bit1_nonneg [`h₁]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `Int.nat_abs_bit1_nonneg [`h₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.nat_abs_bit1_nonneg [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.nat_abs_bit1_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h₂)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
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
    nat_abs_bit1_nonneg_step
    { a : Int } { n : Nat } ( h₁ : 0 ≤ a ) ( h₂ : natAbs a = n ) : natAbs bit1 a = bit1 n
    := by rw [ ← h₂ ] apply Int.nat_abs_bit1_nonneg h₁

end Int

