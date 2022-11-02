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

def NonNeg (a : ℤ) : Prop :=
  Int.casesOn a (fun n => True) fun n => False

protected def le (a b : ℤ) : Prop :=
  NonNeg (b - a)

instance : LE Int :=
  ⟨Int.le⟩

protected def lt (a b : ℤ) : Prop :=
  a + 1 ≤ b

instance : LT Int :=
  ⟨Int.lt⟩

def decidableNonneg (a : ℤ) : Decidable (NonNeg a) :=
  Int.casesOn a (fun a => Decidable.true) fun a => Decidable.false

instance decidableLe (a b : ℤ) : Decidable (a ≤ b) :=
  decidableNonneg _

instance decidableLt (a b : ℤ) : Decidable (a < b) :=
  decidableNonneg _

theorem lt_iff_add_one_le (a b : ℤ) : a < b ↔ a + 1 ≤ b :=
  Iff.refl _

theorem NonNeg.elim {a : ℤ} : NonNeg a → ∃ n : ℕ, a = n :=
  Int.casesOn a (fun n H => Exists.intro n rfl) fun n' => False.elim

theorem nonneg_or_nonneg_neg (a : ℤ) : NonNeg a ∨ NonNeg (-a) :=
  Int.casesOn a (fun n => Or.inl trivial) fun n => Or.inr trivial

theorem le.intro_sub {a b : ℤ} {n : ℕ} (h : b - a = n) : a ≤ b :=
  show NonNeg (b - a) by rw [h] <;> trivial

attribute [local simp]
  Int.sub_eq_add_neg Int.add_assoc Int.add_right_neg Int.add_left_neg Int.zero_add Int.add_zero Int.neg_add Int.neg_neg Int.neg_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `le.intro [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Int.termℤ "ℤ")] "}")
        (Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_=_» («term_+_» `a "+" `n) "=" `b)] [] ")")]
       (Term.typeSpec ":" («term_≤_» `a "≤" `b)))
      (Command.declValSimple
       ":="
       (Term.app
        `le.intro_sub
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h) "," (Tactic.rwRule [] `Int.add_comm)] "]")
               [])
              "<;>"
              (Tactic.simp "simp" [] [] [] [] []))])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.intro_sub
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h) "," (Tactic.rwRule [] `Int.add_comm)] "]")
              [])
             "<;>"
             (Tactic.simp "simp" [] [] [] [] []))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h) "," (Tactic.rwRule [] `Int.add_comm)] "]")
            [])
           "<;>"
           (Tactic.simp "simp" [] [] [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h) "," (Tactic.rwRule [] `Int.add_comm)] "]")
        [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h) "," (Tactic.rwRule [] `Int.add_comm)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
theorem le.intro { a b : ℤ } { n : ℕ } ( h : a + n = b ) : a ≤ b := le.intro_sub by rw [ ← h , Int.add_comm ] <;> simp

theorem le.dest_sub {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, b - a = n :=
  NonNeg.elim h

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `le.dest [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `a "≤" `b)] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
         ","
         («term_=_» («term_+_» `a "+" `n) "=" `b))))
      (Command.declValSimple
       ":="
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] (Term.app `le.dest_sub [`h]))]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.anonymousCtor "⟨" [`n "," `h₁] "⟩")]]
           "=>"
           (Term.app
            `Exists.intro
            [`n
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h₁) "," (Tactic.rwRule [] `Int.add_comm)] "]")
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])])))]))]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] (Term.app `le.dest_sub [`h]))]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.anonymousCtor "⟨" [`n "," `h₁] "⟩")]]
          "=>"
          (Term.app
           `Exists.intro
           [`n
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h₁) "," (Tactic.rwRule [] `Int.add_comm)] "]")
                 [])
                []
                (Tactic.simp "simp" [] [] [] [] [])])))]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Exists.intro
       [`n
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h₁) "," (Tactic.rwRule [] `Int.add_comm)] "]")
             [])
            []
            (Tactic.simp "simp" [] [] [] [] [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h₁) "," (Tactic.rwRule [] `Int.add_comm)] "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h₁) "," (Tactic.rwRule [] `Int.add_comm)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
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
  le.dest
  { a b : ℤ } ( h : a ≤ b ) : ∃ n : ℕ , a + n = b
  := match le.dest_sub h with | ⟨ n , h₁ ⟩ => Exists.intro n by rw [ ← h₁ , Int.add_comm ] simp

theorem le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
  Exists.elim (le.dest h) h'

protected theorem le_total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
  Or.imp_right
    (fun H : NonNeg (-(b - a)) =>
      have : -(b - a) = a - b := by simp [Int.add_comm]
      show NonNeg (a - b) from this ▸ H)
    (nonneg_or_nonneg_neg (b - a))

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_nat_le_coe_nat_of_le [])
      (Command.declSig
       [(Term.implicitBinder "{" [`m `n] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `m "≤" `n)] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.paren "(" [(coeNotation "↑" `m) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]] ")")
         "≤"
         (coeNotation "↑" `n))))
      (Command.declValSimple
       ":="
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] (Term.app `Nat.le.dest [`h]))]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.anonymousCtor
              "⟨"
              [`k "," (Term.paren "(" [`hk [(Term.typeAscription ":" («term_=_» («term_+_» `m "+" `k) "=" `n))]] ")")]
              "⟩")]]
           "=>"
           (Term.app
            `le.intro
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hk)] "]") [])
                 []
                 (Tactic.tacticRfl "rfl")])))]))]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] (Term.app `Nat.le.dest [`h]))]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.anonymousCtor
             "⟨"
             [`k "," (Term.paren "(" [`hk [(Term.typeAscription ":" («term_=_» («term_+_» `m "+" `k) "=" `n))]] ")")]
             "⟩")]]
          "=>"
          (Term.app
           `le.intro
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hk)] "]") [])
                []
                (Tactic.tacticRfl "rfl")])))]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.intro
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hk)] "]") [])
            []
            (Tactic.tacticRfl "rfl")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hk)] "]") [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hk)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
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
  coe_nat_le_coe_nat_of_le
  { m n : ℕ } ( h : m ≤ n ) : ( ↑ m : ℤ ) ≤ ↑ n
  := match Nat.le.dest h with | ⟨ k , ( hk : m + k = n ) ⟩ => le.intro by rw [ ← hk ] rfl

theorem le_of_coe_nat_le_coe_nat {m n : ℕ} (h : (↑m : ℤ) ≤ ↑n) : m ≤ n :=
  le.elim h fun k => fun hk : ↑m + ↑k = ↑n =>
    have : m + k = n := Int.coe_nat_inj ((Int.coe_nat_add m k).trans hk)
    Nat.le.intro this

theorem coe_nat_le_coe_nat_iff (m n : ℕ) : (↑m : ℤ) ≤ ↑n ↔ m ≤ n :=
  Iff.intro le_of_coe_nat_le_coe_nat coe_nat_le_coe_nat_of_le

theorem coe_zero_le (n : ℕ) : 0 ≤ (↑n : ℤ) :=
  coe_nat_le_coe_nat_of_le n.zero_le

theorem eq_coe_of_zero_le {a : ℤ} (h : 0 ≤ a) : ∃ n : ℕ, a = n := by
  have t := le.dest_sub h
  simp at t
  exact t

theorem eq_succ_of_zero_lt {a : ℤ} (h : 0 < a) : ∃ n : ℕ, a = n.succ :=
  let ⟨n, (h : ↑(1 + n) = a)⟩ := le.dest h
  ⟨n, by rw [Nat.add_comm] at h <;> exact h.symm⟩

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + ↑(Nat.succ n) :=
  le.intro
    (show a + 1 + n = a + Nat.succ n by
      simp [Int.coe_nat_eq, Int.add_comm, Int.add_left_comm]
      rfl)

theorem lt.intro {a b : ℤ} {n : ℕ} (h : a + Nat.succ n = b) : a < b :=
  h ▸ lt_add_succ a n

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lt.dest [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_<_» `a "<" `b)] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
         ","
         («term_=_» («term_+_» `a "+" (coeNotation "↑" (Term.app `Nat.succ [`n]))) "=" `b))))
      (Command.declValSimple
       ":="
       (Term.app
        `le.elim
        [`h
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (Term.fun
            "fun"
            (Term.basicFun
             [`hn]
             [(Term.typeSpec ":" («term_=_» («term_+_» («term_+_» `a "+" (num "1")) "+" `n) "=" `b))]
             "=>"
             (Term.app
              `Exists.intro
              [`n
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `hn)
                      ","
                      (Tactic.rwRule [] `Int.add_assoc)
                      ","
                      (Tactic.rwRule [] (Term.app `Int.add_comm [(num "1")]))]
                     "]")
                    [])
                   []
                   (Tactic.tacticRfl "rfl")])))])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.elim
       [`h
        (Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`hn]
            [(Term.typeSpec ":" («term_=_» («term_+_» («term_+_» `a "+" (num "1")) "+" `n) "=" `b))]
            "=>"
            (Term.app
             `Exists.intro
             [`n
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `hn)
                     ","
                     (Tactic.rwRule [] `Int.add_assoc)
                     ","
                     (Tactic.rwRule [] (Term.app `Int.add_comm [(num "1")]))]
                    "]")
                   [])
                  []
                  (Tactic.tacticRfl "rfl")])))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`hn]
          [(Term.typeSpec ":" («term_=_» («term_+_» («term_+_» `a "+" (num "1")) "+" `n) "=" `b))]
          "=>"
          (Term.app
           `Exists.intro
           [`n
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] `hn)
                   ","
                   (Tactic.rwRule [] `Int.add_assoc)
                   ","
                   (Tactic.rwRule [] (Term.app `Int.add_comm [(num "1")]))]
                  "]")
                 [])
                []
                (Tactic.tacticRfl "rfl")])))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hn]
        [(Term.typeSpec ":" («term_=_» («term_+_» («term_+_» `a "+" (num "1")) "+" `n) "=" `b))]
        "=>"
        (Term.app
         `Exists.intro
         [`n
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `hn)
                 ","
                 (Tactic.rwRule [] `Int.add_assoc)
                 ","
                 (Tactic.rwRule [] (Term.app `Int.add_comm [(num "1")]))]
                "]")
               [])
              []
              (Tactic.tacticRfl "rfl")])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Exists.intro
       [`n
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `hn)
               ","
               (Tactic.rwRule [] `Int.add_assoc)
               ","
               (Tactic.rwRule [] (Term.app `Int.add_comm [(num "1")]))]
              "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
            [(Tactic.rwRule ["←"] `hn)
             ","
             (Tactic.rwRule [] `Int.add_assoc)
             ","
             (Tactic.rwRule [] (Term.app `Int.add_comm [(num "1")]))]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `hn)
         ","
         (Tactic.rwRule [] `Int.add_assoc)
         ","
         (Tactic.rwRule [] (Term.app `Int.add_comm [(num "1")]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.add_comm [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
theorem
  lt.dest
  { a b : ℤ } ( h : a < b ) : ∃ n : ℕ , a + ↑ Nat.succ n = b
  := le.elim h fun n => fun hn : a + 1 + n = b => Exists.intro n by rw [ ← hn , Int.add_assoc , Int.add_comm 1 ] rfl

theorem lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(Nat.succ n) = b → P) : P :=
  Exists.elim (lt.dest h) h'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_nat_lt_coe_nat_iff [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n `m] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (Term.paren "(" [(coeNotation "↑" `n) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]] ")")
          "<"
          (coeNotation "↑" `m))
         "↔"
         («term_<_» `n "<" `m))))
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
             [(Tactic.rwRule [] `lt_iff_add_one_le)
              ","
              (Tactic.rwRule ["←"] `Int.coe_nat_succ)
              ","
              (Tactic.rwRule [] `coe_nat_le_coe_nat_iff)]
             "]")
            [])
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `lt_iff_add_one_le)
             ","
             (Tactic.rwRule ["←"] `Int.coe_nat_succ)
             ","
             (Tactic.rwRule [] `coe_nat_le_coe_nat_iff)]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `lt_iff_add_one_le)
         ","
         (Tactic.rwRule ["←"] `Int.coe_nat_succ)
         ","
         (Tactic.rwRule [] `coe_nat_le_coe_nat_iff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_nat_le_coe_nat_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_nat_succ
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
  coe_nat_lt_coe_nat_iff
  ( n m : ℕ ) : ( ↑ n : ℤ ) < ↑ m ↔ n < m
  := by rw [ lt_iff_add_one_le , ← Int.coe_nat_succ , coe_nat_le_coe_nat_iff ] rfl

theorem lt_of_coe_nat_lt_coe_nat {m n : ℕ} (h : (↑m : ℤ) < ↑n) : m < n :=
  (coe_nat_lt_coe_nat_iff _ _).mp h

theorem coe_nat_lt_coe_nat_of_lt {m n : ℕ} (h : m < n) : (↑m : ℤ) < ↑n :=
  (coe_nat_lt_coe_nat_iff _ _).mpr h

-- show that the integers form an ordered additive group
protected theorem le_refl (a : ℤ) : a ≤ a :=
  le.intro (Int.add_zero a)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `le_trans [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b `c] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h₁] [":" («term_≤_» `a "≤" `b)] [] ")")
        (Term.explicitBinder "(" [`h₂] [":" («term_≤_» `b "≤" `c)] [] ")")]
       (Term.typeSpec ":" («term_≤_» `a "≤" `c)))
      (Command.declValSimple
       ":="
       (Term.app
        `le.elim
        [`h₁
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (Term.fun
            "fun"
            (Term.basicFun
             [`hn]
             [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
             "=>"
             (Term.app
              `le.elim
              [`h₂
               (Term.fun
                "fun"
                (Term.basicFun
                 [`m]
                 []
                 "=>"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`hm]
                   [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `c))]
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.apply "apply" `le.intro)
                       []
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule ["←"] `hm) "," (Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule [] `Int.add_assoc)]
                         "]")
                        [])
                       []
                       (Tactic.tacticRfl "rfl")])))))))])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.elim
       [`h₁
        (Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`hn]
            [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
            "=>"
            (Term.app
             `le.elim
             [`h₂
              (Term.fun
               "fun"
               (Term.basicFun
                [`m]
                []
                "=>"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`hm]
                  [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `c))]
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.apply "apply" `le.intro)
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule ["←"] `hm) "," (Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule [] `Int.add_assoc)]
                        "]")
                       [])
                      []
                      (Tactic.tacticRfl "rfl")])))))))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`hn]
          [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
          "=>"
          (Term.app
           `le.elim
           [`h₂
            (Term.fun
             "fun"
             (Term.basicFun
              [`m]
              []
              "=>"
              (Term.fun
               "fun"
               (Term.basicFun
                [`hm]
                [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `c))]
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.apply "apply" `le.intro)
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule ["←"] `hm) "," (Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule [] `Int.add_assoc)]
                      "]")
                     [])
                    []
                    (Tactic.tacticRfl "rfl")])))))))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hn]
        [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
        "=>"
        (Term.app
         `le.elim
         [`h₂
          (Term.fun
           "fun"
           (Term.basicFun
            [`m]
            []
            "=>"
            (Term.fun
             "fun"
             (Term.basicFun
              [`hm]
              [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `c))]
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.apply "apply" `le.intro)
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] `hm) "," (Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule [] `Int.add_assoc)]
                    "]")
                   [])
                  []
                  (Tactic.tacticRfl "rfl")])))))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.elim
       [`h₂
        (Term.fun
         "fun"
         (Term.basicFun
          [`m]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`hm]
            [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `c))]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.apply "apply" `le.intro)
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] `hm) "," (Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule [] `Int.add_assoc)]
                  "]")
                 [])
                []
                (Tactic.tacticRfl "rfl")])))))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`m]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`hm]
          [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `c))]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.apply "apply" `le.intro)
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `hm) "," (Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule [] `Int.add_assoc)]
                "]")
               [])
              []
              (Tactic.tacticRfl "rfl")])))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hm]
        [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `c))]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.apply "apply" `le.intro)
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `hm) "," (Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule [] `Int.add_assoc)]
              "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply "apply" `le.intro)
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `hm) "," (Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule [] `Int.add_assoc)]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `hm) "," (Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule [] `Int.add_assoc)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
    le_trans
    { a b c : ℤ } ( h₁ : a ≤ b ) ( h₂ : b ≤ c ) : a ≤ c
    :=
      le.elim
        h₁
          fun
            n
              =>
              fun
                hn
                  : a + n = b
                  =>
                  le.elim h₂ fun m => fun hm : b + m = c => by apply le.intro rw [ ← hm , ← hn , Int.add_assoc ] rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `le_antisymm [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h₁] [":" («term_≤_» `a "≤" `b)] [] ")")
        (Term.explicitBinder "(" [`h₂] [":" («term_≤_» `b "≤" `a)] [] ")")]
       (Term.typeSpec ":" («term_=_» `a "=" `b)))
      (Command.declValSimple
       ":="
       (Term.app
        `le.elim
        [`h₁
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (Term.fun
            "fun"
            (Term.basicFun
             [`hn]
             [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
             "=>"
             (Term.app
              `le.elim
              [`h₂
               (Term.fun
                "fun"
                (Term.basicFun
                 [`m]
                 []
                 "=>"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`hm]
                   [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `a))]
                   "=>"
                   (Term.have
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      [(Term.typeSpec
                        ":"
                        («term_=_»
                         («term_+_» `a "+" (coeNotation "↑" («term_+_» `n "+" `m)))
                         "="
                         («term_+_» `a "+" (num "0"))))]
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
                            [(Tactic.rwRule [] `Int.coe_nat_add)
                             ","
                             (Tactic.rwRule ["←"] `Int.add_assoc)
                             ","
                             (Tactic.rwRule [] `hn)
                             ","
                             (Tactic.rwRule [] `hm)
                             ","
                             (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                            "]")
                           [])])))))
                    []
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_=_»
                          (Term.paren
                           "("
                           [(coeNotation "↑" («term_+_» `n "+" `m)) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]]
                           ")")
                          "="
                          (num "0")))]
                       ":="
                       (Term.app `Int.add_left_cancel [`this])))
                     []
                     (Term.have
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec ":" («term_=_» («term_+_» `n "+" `m) "=" (num "0")))]
                        ":="
                        (Term.app `Int.coe_nat_inj [`this])))
                      []
                      (Term.have
                       "have"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         []
                         [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                         ":="
                         (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
                       []
                       (Term.show
                        "show"
                        («term_=_» `a "=" `b)
                        (Term.byTactic'
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule ["←"] `hn)
                               ","
                               (Tactic.rwRule [] `this)
                               ","
                               (Tactic.rwRule [] `Int.coe_nat_zero)
                               ","
                               (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                              "]")
                             [])]))))))))))))])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.elim
       [`h₁
        (Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`hn]
            [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
            "=>"
            (Term.app
             `le.elim
             [`h₂
              (Term.fun
               "fun"
               (Term.basicFun
                [`m]
                []
                "=>"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`hm]
                  [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `a))]
                  "=>"
                  (Term.have
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        («term_+_» `a "+" (coeNotation "↑" («term_+_» `n "+" `m)))
                        "="
                        («term_+_» `a "+" (num "0"))))]
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
                           [(Tactic.rwRule [] `Int.coe_nat_add)
                            ","
                            (Tactic.rwRule ["←"] `Int.add_assoc)
                            ","
                            (Tactic.rwRule [] `hn)
                            ","
                            (Tactic.rwRule [] `hm)
                            ","
                            (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                           "]")
                          [])])))))
                   []
                   (Term.have
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      [(Term.typeSpec
                        ":"
                        («term_=_»
                         (Term.paren
                          "("
                          [(coeNotation "↑" («term_+_» `n "+" `m)) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]]
                          ")")
                         "="
                         (num "0")))]
                      ":="
                      (Term.app `Int.add_left_cancel [`this])))
                    []
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec ":" («term_=_» («term_+_» `n "+" `m) "=" (num "0")))]
                       ":="
                       (Term.app `Int.coe_nat_inj [`this])))
                     []
                     (Term.have
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                        ":="
                        (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
                      []
                      (Term.show
                       "show"
                       («term_=_» `a "=" `b)
                       (Term.byTactic'
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule ["←"] `hn)
                              ","
                              (Tactic.rwRule [] `this)
                              ","
                              (Tactic.rwRule [] `Int.coe_nat_zero)
                              ","
                              (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                             "]")
                            [])]))))))))))))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`hn]
          [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
          "=>"
          (Term.app
           `le.elim
           [`h₂
            (Term.fun
             "fun"
             (Term.basicFun
              [`m]
              []
              "=>"
              (Term.fun
               "fun"
               (Term.basicFun
                [`hm]
                [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `a))]
                "=>"
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      («term_+_» `a "+" (coeNotation "↑" («term_+_» `n "+" `m)))
                      "="
                      («term_+_» `a "+" (num "0"))))]
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
                         [(Tactic.rwRule [] `Int.coe_nat_add)
                          ","
                          (Tactic.rwRule ["←"] `Int.add_assoc)
                          ","
                          (Tactic.rwRule [] `hn)
                          ","
                          (Tactic.rwRule [] `hm)
                          ","
                          (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                         "]")
                        [])])))))
                 []
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Term.paren
                        "("
                        [(coeNotation "↑" («term_+_» `n "+" `m)) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]]
                        ")")
                       "="
                       (num "0")))]
                    ":="
                    (Term.app `Int.add_left_cancel [`this])))
                  []
                  (Term.have
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec ":" («term_=_» («term_+_» `n "+" `m) "=" (num "0")))]
                     ":="
                     (Term.app `Int.coe_nat_inj [`this])))
                   []
                   (Term.have
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                      ":="
                      (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
                    []
                    (Term.show
                     "show"
                     («term_=_» `a "=" `b)
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule ["←"] `hn)
                            ","
                            (Tactic.rwRule [] `this)
                            ","
                            (Tactic.rwRule [] `Int.coe_nat_zero)
                            ","
                            (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                           "]")
                          [])]))))))))))))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hn]
        [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
        "=>"
        (Term.app
         `le.elim
         [`h₂
          (Term.fun
           "fun"
           (Term.basicFun
            [`m]
            []
            "=>"
            (Term.fun
             "fun"
             (Term.basicFun
              [`hm]
              [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `a))]
              "=>"
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    («term_+_» `a "+" (coeNotation "↑" («term_+_» `n "+" `m)))
                    "="
                    («term_+_» `a "+" (num "0"))))]
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
                       [(Tactic.rwRule [] `Int.coe_nat_add)
                        ","
                        (Tactic.rwRule ["←"] `Int.add_assoc)
                        ","
                        (Tactic.rwRule [] `hn)
                        ","
                        (Tactic.rwRule [] `hm)
                        ","
                        (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                       "]")
                      [])])))))
               []
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Term.paren
                      "("
                      [(coeNotation "↑" («term_+_» `n "+" `m)) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]]
                      ")")
                     "="
                     (num "0")))]
                  ":="
                  (Term.app `Int.add_left_cancel [`this])))
                []
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec ":" («term_=_» («term_+_» `n "+" `m) "=" (num "0")))]
                   ":="
                   (Term.app `Int.coe_nat_inj [`this])))
                 []
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                    ":="
                    (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
                  []
                  (Term.show
                   "show"
                   («term_=_» `a "=" `b)
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule ["←"] `hn)
                          ","
                          (Tactic.rwRule [] `this)
                          ","
                          (Tactic.rwRule [] `Int.coe_nat_zero)
                          ","
                          (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                         "]")
                        [])]))))))))))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.elim
       [`h₂
        (Term.fun
         "fun"
         (Term.basicFun
          [`m]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`hm]
            [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `a))]
            "=>"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  («term_+_» `a "+" (coeNotation "↑" («term_+_» `n "+" `m)))
                  "="
                  («term_+_» `a "+" (num "0"))))]
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
                     [(Tactic.rwRule [] `Int.coe_nat_add)
                      ","
                      (Tactic.rwRule ["←"] `Int.add_assoc)
                      ","
                      (Tactic.rwRule [] `hn)
                      ","
                      (Tactic.rwRule [] `hm)
                      ","
                      (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                     "]")
                    [])])))))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.paren
                    "("
                    [(coeNotation "↑" («term_+_» `n "+" `m)) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]]
                    ")")
                   "="
                   (num "0")))]
                ":="
                (Term.app `Int.add_left_cancel [`this])))
              []
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec ":" («term_=_» («term_+_» `n "+" `m) "=" (num "0")))]
                 ":="
                 (Term.app `Int.coe_nat_inj [`this])))
               []
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                  ":="
                  (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
                []
                (Term.show
                 "show"
                 («term_=_» `a "=" `b)
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule ["←"] `hn)
                        ","
                        (Tactic.rwRule [] `this)
                        ","
                        (Tactic.rwRule [] `Int.coe_nat_zero)
                        ","
                        (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                       "]")
                      [])]))))))))))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`m]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`hm]
          [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `a))]
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_» («term_+_» `a "+" (coeNotation "↑" («term_+_» `n "+" `m))) "=" («term_+_» `a "+" (num "0"))))]
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
                   [(Tactic.rwRule [] `Int.coe_nat_add)
                    ","
                    (Tactic.rwRule ["←"] `Int.add_assoc)
                    ","
                    (Tactic.rwRule [] `hn)
                    ","
                    (Tactic.rwRule [] `hm)
                    ","
                    (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                   "]")
                  [])])))))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.paren
                  "("
                  [(coeNotation "↑" («term_+_» `n "+" `m)) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]]
                  ")")
                 "="
                 (num "0")))]
              ":="
              (Term.app `Int.add_left_cancel [`this])))
            []
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_=_» («term_+_» `n "+" `m) "=" (num "0")))]
               ":="
               (Term.app `Int.coe_nat_inj [`this])))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                ":="
                (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
              []
              (Term.show
               "show"
               («term_=_» `a "=" `b)
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `hn)
                      ","
                      (Tactic.rwRule [] `this)
                      ","
                      (Tactic.rwRule [] `Int.coe_nat_zero)
                      ","
                      (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                     "]")
                    [])]))))))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hm]
        [(Term.typeSpec ":" («term_=_» («term_+_» `b "+" `m) "=" `a))]
        "=>"
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_» («term_+_» `a "+" (coeNotation "↑" («term_+_» `n "+" `m))) "=" («term_+_» `a "+" (num "0"))))]
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
                 [(Tactic.rwRule [] `Int.coe_nat_add)
                  ","
                  (Tactic.rwRule ["←"] `Int.add_assoc)
                  ","
                  (Tactic.rwRule [] `hn)
                  ","
                  (Tactic.rwRule [] `hm)
                  ","
                  (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                 "]")
                [])])))))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              («term_=_»
               (Term.paren
                "("
                [(coeNotation "↑" («term_+_» `n "+" `m)) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]]
                ")")
               "="
               (num "0")))]
            ":="
            (Term.app `Int.add_left_cancel [`this])))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" («term_=_» («term_+_» `n "+" `m) "=" (num "0")))]
             ":="
             (Term.app `Int.coe_nat_inj [`this])))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
              ":="
              (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
            []
            (Term.show
             "show"
             («term_=_» `a "=" `b)
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule ["←"] `hn)
                    ","
                    (Tactic.rwRule [] `this)
                    ","
                    (Tactic.rwRule [] `Int.coe_nat_zero)
                    ","
                    (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                   "]")
                  [])]))))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_» («term_+_» `a "+" (coeNotation "↑" («term_+_» `n "+" `m))) "=" («term_+_» `a "+" (num "0"))))]
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
               [(Tactic.rwRule [] `Int.coe_nat_add)
                ","
                (Tactic.rwRule ["←"] `Int.add_assoc)
                ","
                (Tactic.rwRule [] `hn)
                ","
                (Tactic.rwRule [] `hm)
                ","
                (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
               "]")
              [])])))))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.paren "(" [(coeNotation "↑" («term_+_» `n "+" `m)) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]] ")")
             "="
             (num "0")))]
          ":="
          (Term.app `Int.add_left_cancel [`this])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" («term_=_» («term_+_» `n "+" `m) "=" (num "0")))]
           ":="
           (Term.app `Int.coe_nat_inj [`this])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
            ":="
            (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
          []
          (Term.show
           "show"
           («term_=_» `a "=" `b)
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `hn)
                  ","
                  (Tactic.rwRule [] `this)
                  ","
                  (Tactic.rwRule [] `Int.coe_nat_zero)
                  ","
                  (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                 "]")
                [])]))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.paren "(" [(coeNotation "↑" («term_+_» `n "+" `m)) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]] ")")
            "="
            (num "0")))]
         ":="
         (Term.app `Int.add_left_cancel [`this])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_=_» («term_+_» `n "+" `m) "=" (num "0")))]
          ":="
          (Term.app `Int.coe_nat_inj [`this])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
           ":="
           (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
         []
         (Term.show
          "show"
          («term_=_» `a "=" `b)
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `hn)
                 ","
                 (Tactic.rwRule [] `this)
                 ","
                 (Tactic.rwRule [] `Int.coe_nat_zero)
                 ","
                 (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
                "]")
               [])])))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_=_» («term_+_» `n "+" `m) "=" (num "0")))]
         ":="
         (Term.app `Int.coe_nat_inj [`this])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
          ":="
          (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
        []
        (Term.show
         "show"
         («term_=_» `a "=" `b)
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] `hn)
                ","
                (Tactic.rwRule [] `this)
                ","
                (Tactic.rwRule [] `Int.coe_nat_zero)
                ","
                (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
               "]")
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
         ":="
         (Term.app `Nat.eq_zero_of_add_eq_zero_right [`this])))
       []
       (Term.show
        "show"
        («term_=_» `a "=" `b)
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `hn)
               ","
               (Tactic.rwRule [] `this)
               ","
               (Tactic.rwRule [] `Int.coe_nat_zero)
               ","
               (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
              "]")
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_» `a "=" `b)
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule ["←"] `hn)
              ","
              (Tactic.rwRule [] `this)
              ","
              (Tactic.rwRule [] `Int.coe_nat_zero)
              ","
              (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
             "]")
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `hn)
         ","
         (Tactic.rwRule [] `this)
         ","
         (Tactic.rwRule [] `Int.coe_nat_zero)
         ","
         (Tactic.rwRule [] (Term.app `Int.add_zero [`a]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.add_zero [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.add_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_nat_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
    le_antisymm
    { a b : ℤ } ( h₁ : a ≤ b ) ( h₂ : b ≤ a ) : a = b
    :=
      le.elim
        h₁
          fun
            n
              =>
              fun
                hn
                  : a + n = b
                  =>
                  le.elim
                    h₂
                      fun
                        m
                          =>
                          fun
                            hm
                              : b + m = a
                              =>
                              have
                                : a + ↑ n + m = a + 0
                                  :=
                                  by rw [ Int.coe_nat_add , ← Int.add_assoc , hn , hm , Int.add_zero a ]
                                have
                                  : ( ↑ n + m : ℤ ) = 0 := Int.add_left_cancel this
                                  have
                                    : n + m = 0 := Int.coe_nat_inj this
                                    have
                                      : n = 0 := Nat.eq_zero_of_add_eq_zero_right this
                                      show a = b by rw [ ← hn , this , Int.coe_nat_zero , Int.add_zero a ]

protected theorem lt_irrefl (a : ℤ) : ¬a < a := fun this : a < a =>
  lt.elim this fun n => fun hn : a + Nat.succ n = a =>
    have : a + Nat.succ n = a + 0 := by rw [hn, Int.add_zero]
    have : Nat.succ n = 0 := Int.coe_nat_inj (Int.add_left_cancel this)
    show False from Nat.succ_ne_zero _ this

protected theorem ne_of_lt {a b : ℤ} (h : a < b) : a ≠ b := fun this : a = b =>
  absurd
    (by
      rw [this] at h
      exact h)
    (Int.lt_irrefl b)

theorem le_of_lt {a b : ℤ} (h : a < b) : a ≤ b :=
  lt.elim h fun n => fun hn : a + Nat.succ n = b => le.intro hn

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lt_iff_le_and_ne [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b] [":" (Int.termℤ "ℤ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_» («term_<_» `a "<" `b) "↔" («term_∧_» («term_≤_» `a "≤" `b) "∧" («term_≠_» `a "≠" `b)))))
      (Command.declValSimple
       ":="
       (Term.app
        `Iff.intro
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.anonymousCtor "⟨" [(Term.app `le_of_lt [`h]) "," (Term.app `Int.ne_of_lt [`h])] "⟩")))
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [`aleb "," `aneb] "⟩")]
           []
           "=>"
           (Term.app
            `le.elim
            [`aleb
             (Term.fun
              "fun"
              (Term.basicFun
               [`n]
               []
               "=>"
               (Term.fun
                "fun"
                (Term.basicFun
                 [`hn]
                 [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
                 "=>"
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec ":" («term_≠_» `n "≠" (num "0")))]
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`this]
                      [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                      "=>"
                      (Term.app
                       `aneb
                       [(Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule ["←"] `hn)
                               ","
                               (Tactic.rwRule [] `this)
                               ","
                               (Tactic.rwRule [] `Int.coe_nat_zero)
                               ","
                               (Tactic.rwRule [] `Int.add_zero)]
                              "]")
                             [])])))])))))
                  []
                  (Term.have
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec ":" («term_=_» `n "=" (Term.app `Nat.succ [(Term.app `Nat.pred [`n])])))]
                     ":="
                     (Term.app
                      `Eq.symm
                      [(Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.pos_of_ne_zero [`this])])])))
                   []
                   (Term.app
                    `lt.intro
                    [(Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
                          [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                         []
                         (Tactic.exact "exact" `hn)])))])))))))])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Iff.intro
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.anonymousCtor "⟨" [(Term.app `le_of_lt [`h]) "," (Term.app `Int.ne_of_lt [`h])] "⟩")))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`aleb "," `aneb] "⟩")]
          []
          "=>"
          (Term.app
           `le.elim
           [`aleb
            (Term.fun
             "fun"
             (Term.basicFun
              [`n]
              []
              "=>"
              (Term.fun
               "fun"
               (Term.basicFun
                [`hn]
                [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
                "=>"
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec ":" («term_≠_» `n "≠" (num "0")))]
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`this]
                     [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                     "=>"
                     (Term.app
                      `aneb
                      [(Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule ["←"] `hn)
                              ","
                              (Tactic.rwRule [] `this)
                              ","
                              (Tactic.rwRule [] `Int.coe_nat_zero)
                              ","
                              (Tactic.rwRule [] `Int.add_zero)]
                             "]")
                            [])])))])))))
                 []
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec ":" («term_=_» `n "=" (Term.app `Nat.succ [(Term.app `Nat.pred [`n])])))]
                    ":="
                    (Term.app `Eq.symm [(Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.pos_of_ne_zero [`this])])])))
                  []
                  (Term.app
                   `lt.intro
                   [(Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
                         [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                        []
                        (Tactic.exact "exact" `hn)])))])))))))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`aleb "," `aneb] "⟩")]
        []
        "=>"
        (Term.app
         `le.elim
         [`aleb
          (Term.fun
           "fun"
           (Term.basicFun
            [`n]
            []
            "=>"
            (Term.fun
             "fun"
             (Term.basicFun
              [`hn]
              [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
              "=>"
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec ":" («term_≠_» `n "≠" (num "0")))]
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`this]
                   [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                   "=>"
                   (Term.app
                    `aneb
                    [(Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule ["←"] `hn)
                            ","
                            (Tactic.rwRule [] `this)
                            ","
                            (Tactic.rwRule [] `Int.coe_nat_zero)
                            ","
                            (Tactic.rwRule [] `Int.add_zero)]
                           "]")
                          [])])))])))))
               []
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec ":" («term_=_» `n "=" (Term.app `Nat.succ [(Term.app `Nat.pred [`n])])))]
                  ":="
                  (Term.app `Eq.symm [(Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.pos_of_ne_zero [`this])])])))
                []
                (Term.app
                 `lt.intro
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
                       [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                      []
                      (Tactic.exact "exact" `hn)])))])))))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.elim
       [`aleb
        (Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`hn]
            [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
            "=>"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_≠_» `n "≠" (num "0")))]
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`this]
                 [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                 "=>"
                 (Term.app
                  `aneb
                  [(Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule ["←"] `hn)
                          ","
                          (Tactic.rwRule [] `this)
                          ","
                          (Tactic.rwRule [] `Int.coe_nat_zero)
                          ","
                          (Tactic.rwRule [] `Int.add_zero)]
                         "]")
                        [])])))])))))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_=_» `n "=" (Term.app `Nat.succ [(Term.app `Nat.pred [`n])])))]
                ":="
                (Term.app `Eq.symm [(Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.pos_of_ne_zero [`this])])])))
              []
              (Term.app
               `lt.intro
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                    []
                    (Tactic.exact "exact" `hn)])))])))))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`hn]
          [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" («term_≠_» `n "≠" (num "0")))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`this]
               [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
               "=>"
               (Term.app
                `aneb
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule ["←"] `hn)
                        ","
                        (Tactic.rwRule [] `this)
                        ","
                        (Tactic.rwRule [] `Int.coe_nat_zero)
                        ","
                        (Tactic.rwRule [] `Int.add_zero)]
                       "]")
                      [])])))])))))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" («term_=_» `n "=" (Term.app `Nat.succ [(Term.app `Nat.pred [`n])])))]
              ":="
              (Term.app `Eq.symm [(Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.pos_of_ne_zero [`this])])])))
            []
            (Term.app
             `lt.intro
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                  []
                  (Tactic.exact "exact" `hn)])))])))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hn]
        [(Term.typeSpec ":" («term_=_» («term_+_» `a "+" `n) "=" `b))]
        "=>"
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" («term_≠_» `n "≠" (num "0")))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`this]
             [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
             "=>"
             (Term.app
              `aneb
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] `hn)
                      ","
                      (Tactic.rwRule [] `this)
                      ","
                      (Tactic.rwRule [] `Int.coe_nat_zero)
                      ","
                      (Tactic.rwRule [] `Int.add_zero)]
                     "]")
                    [])])))])))))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec ":" («term_=_» `n "=" (Term.app `Nat.succ [(Term.app `Nat.pred [`n])])))]
            ":="
            (Term.app `Eq.symm [(Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.pos_of_ne_zero [`this])])])))
          []
          (Term.app
           `lt.intro
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
                []
                (Tactic.exact "exact" `hn)])))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_≠_» `n "≠" (num "0")))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`this]
           [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
           "=>"
           (Term.app
            `aneb
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule ["←"] `hn)
                    ","
                    (Tactic.rwRule [] `this)
                    ","
                    (Tactic.rwRule [] `Int.coe_nat_zero)
                    ","
                    (Tactic.rwRule [] `Int.add_zero)]
                   "]")
                  [])])))])))))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_=_» `n "=" (Term.app `Nat.succ [(Term.app `Nat.pred [`n])])))]
          ":="
          (Term.app `Eq.symm [(Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.pos_of_ne_zero [`this])])])))
        []
        (Term.app
         `lt.intro
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
              []
              (Tactic.exact "exact" `hn)])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_=_» `n "=" (Term.app `Nat.succ [(Term.app `Nat.pred [`n])])))]
         ":="
         (Term.app `Eq.symm [(Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.pos_of_ne_zero [`this])])])))
       []
       (Term.app
        `lt.intro
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
             []
             (Tactic.exact "exact" `hn)])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt.intro
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
            []
            (Tactic.exact "exact" `hn)])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
          []
          (Tactic.exact "exact" `hn)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `hn)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     [(Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hn] []))])
          []
          (Tactic.exact "exact" `hn)])))
      []]
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt.intro
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.symm [(Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.pos_of_ne_zero [`this])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.pos_of_ne_zero [`this])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.pos_of_ne_zero [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.pos_of_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Nat.pos_of_ne_zero [`this]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.succ_pred_eq_of_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     [(Term.app `Nat.succ_pred_eq_of_pos [(Term.paren "(" [(Term.app `Nat.pos_of_ne_zero [`this]) []] ")")]) []]
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `n "=" (Term.app `Nat.succ [(Term.app `Nat.pred [`n])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.succ [(Term.app `Nat.pred [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.pred [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.pred
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Nat.pred [`n]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.succ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`this]
        [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
        "=>"
        (Term.app
         `aneb
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `hn)
                 ","
                 (Tactic.rwRule [] `this)
                 ","
                 (Tactic.rwRule [] `Int.coe_nat_zero)
                 ","
                 (Tactic.rwRule [] `Int.add_zero)]
                "]")
               [])])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `aneb
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `hn)
               ","
               (Tactic.rwRule [] `this)
               ","
               (Tactic.rwRule [] `Int.coe_nat_zero)
               ","
               (Tactic.rwRule [] `Int.add_zero)]
              "]")
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
            [(Tactic.rwRule ["←"] `hn)
             ","
             (Tactic.rwRule [] `this)
             ","
             (Tactic.rwRule [] `Int.coe_nat_zero)
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
        [(Tactic.rwRule ["←"] `hn)
         ","
         (Tactic.rwRule [] `this)
         ","
         (Tactic.rwRule [] `Int.coe_nat_zero)
         ","
         (Tactic.rwRule [] `Int.add_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_nat_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
    lt_iff_le_and_ne
    ( a b : ℤ ) : a < b ↔ a ≤ b ∧ a ≠ b
    :=
      Iff.intro
        fun h => ⟨ le_of_lt h , Int.ne_of_lt h ⟩
          fun
            ⟨ aleb , aneb ⟩
              =>
              le.elim
                aleb
                  fun
                    n
                      =>
                      fun
                        hn
                          : a + n = b
                          =>
                          have
                            : n ≠ 0 := fun this : n = 0 => aneb by rw [ ← hn , this , Int.coe_nat_zero , Int.add_zero ]
                            have
                              : n = Nat.succ Nat.pred n := Eq.symm Nat.succ_pred_eq_of_pos Nat.pos_of_ne_zero this
                              lt.intro by rw [ this ] at hn exact hn

theorem lt_succ (a : ℤ) : a < a + 1 :=
  Int.le_refl (a + 1)

protected theorem add_le_add_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
  le.elim h fun n => fun hn : a + n = b => le.intro (show c + a + n = c + b by rw [Int.add_assoc, hn])

protected theorem add_lt_add_left {a b : ℤ} (h : a < b) (c : ℤ) : c + a < c + b :=
  Iff.mpr (Int.lt_iff_le_and_ne _ _)
    (And.intro (Int.add_le_add_left (le_of_lt h) _) fun heq =>
      Int.lt_irrefl b
        (by
          rw [Int.add_left_cancel HEq] at h
          exact h))

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_nonneg [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`ha] [":" («term_≤_» (num "0") "≤" `a)] [] ")")
        (Term.explicitBinder "(" [`hb] [":" («term_≤_» (num "0") "≤" `b)] [] ")")]
       (Term.typeSpec ":" («term_≤_» (num "0") "≤" («term_*_» `a "*" `b))))
      (Command.declValSimple
       ":="
       (Term.app
        `le.elim
        [`ha
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (Term.fun
            "fun"
            (Term.basicFun
             [`hn]
             []
             "=>"
             (Term.app
              `le.elim
              [`hb
               (Term.fun
                "fun"
                (Term.basicFun
                 [`m]
                 []
                 "=>"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`hm]
                   []
                   "=>"
                   (Term.app
                    `le.intro
                    [(Term.show
                      "show"
                      («term_=_»
                       («term_+_» (num "0") "+" («term_*_» (coeNotation "↑" `n) "*" (coeNotation "↑" `m)))
                       "="
                       («term_*_» `a "*" `b))
                      (Term.byTactic'
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                           [])
                          []
                          (Tactic.simp
                           "simp"
                           []
                           []
                           []
                           ["[" [(Tactic.simpLemma [] [] `Int.zero_add)] "]"]
                           [])]))))])))))])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.elim
       [`ha
        (Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`hn]
            []
            "=>"
            (Term.app
             `le.elim
             [`hb
              (Term.fun
               "fun"
               (Term.basicFun
                [`m]
                []
                "=>"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`hm]
                  []
                  "=>"
                  (Term.app
                   `le.intro
                   [(Term.show
                     "show"
                     («term_=_»
                      («term_+_» (num "0") "+" («term_*_» (coeNotation "↑" `n) "*" (coeNotation "↑" `m)))
                      "="
                      («term_*_» `a "*" `b))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                          [])
                         []
                         (Tactic.simp
                          "simp"
                          []
                          []
                          []
                          ["[" [(Tactic.simpLemma [] [] `Int.zero_add)] "]"]
                          [])]))))])))))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`hn]
          []
          "=>"
          (Term.app
           `le.elim
           [`hb
            (Term.fun
             "fun"
             (Term.basicFun
              [`m]
              []
              "=>"
              (Term.fun
               "fun"
               (Term.basicFun
                [`hm]
                []
                "=>"
                (Term.app
                 `le.intro
                 [(Term.show
                   "show"
                   («term_=_»
                    («term_+_» (num "0") "+" («term_*_» (coeNotation "↑" `n) "*" (coeNotation "↑" `m)))
                    "="
                    («term_*_» `a "*" `b))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                        [])
                       []
                       (Tactic.simp
                        "simp"
                        []
                        []
                        []
                        ["[" [(Tactic.simpLemma [] [] `Int.zero_add)] "]"]
                        [])]))))])))))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hn]
        []
        "=>"
        (Term.app
         `le.elim
         [`hb
          (Term.fun
           "fun"
           (Term.basicFun
            [`m]
            []
            "=>"
            (Term.fun
             "fun"
             (Term.basicFun
              [`hm]
              []
              "=>"
              (Term.app
               `le.intro
               [(Term.show
                 "show"
                 («term_=_»
                  («term_+_» (num "0") "+" («term_*_» (coeNotation "↑" `n) "*" (coeNotation "↑" `m)))
                  "="
                  («term_*_» `a "*" `b))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                      [])
                     []
                     (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.zero_add)] "]"] [])]))))])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.elim
       [`hb
        (Term.fun
         "fun"
         (Term.basicFun
          [`m]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`hm]
            []
            "=>"
            (Term.app
             `le.intro
             [(Term.show
               "show"
               («term_=_»
                («term_+_» (num "0") "+" («term_*_» (coeNotation "↑" `n) "*" (coeNotation "↑" `m)))
                "="
                («term_*_» `a "*" `b))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                    [])
                   []
                   (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.zero_add)] "]"] [])]))))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`m]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`hm]
          []
          "=>"
          (Term.app
           `le.intro
           [(Term.show
             "show"
             («term_=_»
              («term_+_» (num "0") "+" («term_*_» (coeNotation "↑" `n) "*" (coeNotation "↑" `m)))
              "="
              («term_*_» `a "*" `b))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.zero_add)] "]"] [])]))))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hm]
        []
        "=>"
        (Term.app
         `le.intro
         [(Term.show
           "show"
           («term_=_»
            («term_+_» (num "0") "+" («term_*_» (coeNotation "↑" `n) "*" (coeNotation "↑" `m)))
            "="
            («term_*_» `a "*" `b))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                [])
               []
               (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.zero_add)] "]"] [])]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le.intro
       [(Term.show
         "show"
         («term_=_»
          («term_+_» (num "0") "+" («term_*_» (coeNotation "↑" `n) "*" (coeNotation "↑" `m)))
          "="
          («term_*_» `a "*" `b))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
              [])
             []
             (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.zero_add)] "]"] [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        («term_+_» (num "0") "+" («term_*_» (coeNotation "↑" `n) "*" (coeNotation "↑" `m)))
        "="
        («term_*_» `a "*" `b))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
            [])
           []
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.zero_add)] "]"] [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.zero_add)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
    mul_nonneg
    { a b : ℤ } ( ha : 0 ≤ a ) ( hb : 0 ≤ b ) : 0 ≤ a * b
    :=
      le.elim
        ha
          fun
            n
              =>
              fun
                hn
                  =>
                  le.elim
                    hb
                      fun m => fun hm => le.intro show 0 + ↑ n * ↑ m = a * b by rw [ ← hn , ← hm ] simp [ Int.zero_add ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_pos [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`ha] [":" («term_<_» (num "0") "<" `a)] [] ")")
        (Term.explicitBinder "(" [`hb] [":" («term_<_» (num "0") "<" `b)] [] ")")]
       (Term.typeSpec ":" («term_<_» (num "0") "<" («term_*_» `a "*" `b))))
      (Command.declValSimple
       ":="
       (Term.app
        `lt.elim
        [`ha
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           (Term.fun
            "fun"
            (Term.basicFun
             [`hn]
             []
             "=>"
             (Term.app
              `lt.elim
              [`hb
               (Term.fun
                "fun"
                (Term.basicFun
                 [`m]
                 []
                 "=>"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`hm]
                   []
                   "=>"
                   (Term.app
                    `lt.intro
                    [(Term.show
                      "show"
                      («term_=_»
                       («term_+_»
                        (num "0")
                        "+"
                        (coeNotation
                         "↑"
                         (Term.app `Nat.succ [(«term_+_» («term_*_» (Term.app `Nat.succ [`n]) "*" `m) "+" `n)])))
                       "="
                       («term_*_» `a "*" `b))
                      (Term.byTactic'
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                           [])
                          []
                          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.coe_nat_zero)] "]"] [])
                          []
                          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.coe_nat_mul)] "]") [])
                          []
                          (Tactic.simp
                           "simp"
                           []
                           []
                           []
                           ["["
                            [(Tactic.simpLemma [] [] `Nat.mul_succ)
                             ","
                             (Tactic.simpLemma [] [] `Nat.add_succ)
                             ","
                             (Tactic.simpLemma [] [] `Nat.succ_add)]
                            "]"]
                           [])]))))])))))])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt.elim
       [`ha
        (Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`hn]
            []
            "=>"
            (Term.app
             `lt.elim
             [`hb
              (Term.fun
               "fun"
               (Term.basicFun
                [`m]
                []
                "=>"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`hm]
                  []
                  "=>"
                  (Term.app
                   `lt.intro
                   [(Term.show
                     "show"
                     («term_=_»
                      («term_+_»
                       (num "0")
                       "+"
                       (coeNotation
                        "↑"
                        (Term.app `Nat.succ [(«term_+_» («term_*_» (Term.app `Nat.succ [`n]) "*" `m) "+" `n)])))
                      "="
                      («term_*_» `a "*" `b))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                          [])
                         []
                         (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.coe_nat_zero)] "]"] [])
                         []
                         (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.coe_nat_mul)] "]") [])
                         []
                         (Tactic.simp
                          "simp"
                          []
                          []
                          []
                          ["["
                           [(Tactic.simpLemma [] [] `Nat.mul_succ)
                            ","
                            (Tactic.simpLemma [] [] `Nat.add_succ)
                            ","
                            (Tactic.simpLemma [] [] `Nat.succ_add)]
                           "]"]
                          [])]))))])))))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`hn]
          []
          "=>"
          (Term.app
           `lt.elim
           [`hb
            (Term.fun
             "fun"
             (Term.basicFun
              [`m]
              []
              "=>"
              (Term.fun
               "fun"
               (Term.basicFun
                [`hm]
                []
                "=>"
                (Term.app
                 `lt.intro
                 [(Term.show
                   "show"
                   («term_=_»
                    («term_+_»
                     (num "0")
                     "+"
                     (coeNotation
                      "↑"
                      (Term.app `Nat.succ [(«term_+_» («term_*_» (Term.app `Nat.succ [`n]) "*" `m) "+" `n)])))
                    "="
                    («term_*_» `a "*" `b))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                        [])
                       []
                       (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.coe_nat_zero)] "]"] [])
                       []
                       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.coe_nat_mul)] "]") [])
                       []
                       (Tactic.simp
                        "simp"
                        []
                        []
                        []
                        ["["
                         [(Tactic.simpLemma [] [] `Nat.mul_succ)
                          ","
                          (Tactic.simpLemma [] [] `Nat.add_succ)
                          ","
                          (Tactic.simpLemma [] [] `Nat.succ_add)]
                         "]"]
                        [])]))))])))))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hn]
        []
        "=>"
        (Term.app
         `lt.elim
         [`hb
          (Term.fun
           "fun"
           (Term.basicFun
            [`m]
            []
            "=>"
            (Term.fun
             "fun"
             (Term.basicFun
              [`hm]
              []
              "=>"
              (Term.app
               `lt.intro
               [(Term.show
                 "show"
                 («term_=_»
                  («term_+_»
                   (num "0")
                   "+"
                   (coeNotation
                    "↑"
                    (Term.app `Nat.succ [(«term_+_» («term_*_» (Term.app `Nat.succ [`n]) "*" `m) "+" `n)])))
                  "="
                  («term_*_» `a "*" `b))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                      [])
                     []
                     (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.coe_nat_zero)] "]"] [])
                     []
                     (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.coe_nat_mul)] "]") [])
                     []
                     (Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["["
                       [(Tactic.simpLemma [] [] `Nat.mul_succ)
                        ","
                        (Tactic.simpLemma [] [] `Nat.add_succ)
                        ","
                        (Tactic.simpLemma [] [] `Nat.succ_add)]
                       "]"]
                      [])]))))])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt.elim
       [`hb
        (Term.fun
         "fun"
         (Term.basicFun
          [`m]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`hm]
            []
            "=>"
            (Term.app
             `lt.intro
             [(Term.show
               "show"
               («term_=_»
                («term_+_»
                 (num "0")
                 "+"
                 (coeNotation
                  "↑"
                  (Term.app `Nat.succ [(«term_+_» («term_*_» (Term.app `Nat.succ [`n]) "*" `m) "+" `n)])))
                "="
                («term_*_» `a "*" `b))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                    [])
                   []
                   (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.coe_nat_zero)] "]"] [])
                   []
                   (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.coe_nat_mul)] "]") [])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["["
                     [(Tactic.simpLemma [] [] `Nat.mul_succ)
                      ","
                      (Tactic.simpLemma [] [] `Nat.add_succ)
                      ","
                      (Tactic.simpLemma [] [] `Nat.succ_add)]
                     "]"]
                    [])]))))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`m]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`hm]
          []
          "=>"
          (Term.app
           `lt.intro
           [(Term.show
             "show"
             («term_=_»
              («term_+_»
               (num "0")
               "+"
               (coeNotation "↑" (Term.app `Nat.succ [(«term_+_» («term_*_» (Term.app `Nat.succ [`n]) "*" `m) "+" `n)])))
              "="
              («term_*_» `a "*" `b))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.coe_nat_zero)] "]"] [])
                 []
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.coe_nat_mul)] "]") [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [] `Nat.mul_succ)
                    ","
                    (Tactic.simpLemma [] [] `Nat.add_succ)
                    ","
                    (Tactic.simpLemma [] [] `Nat.succ_add)]
                   "]"]
                  [])]))))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hm]
        []
        "=>"
        (Term.app
         `lt.intro
         [(Term.show
           "show"
           («term_=_»
            («term_+_»
             (num "0")
             "+"
             (coeNotation "↑" (Term.app `Nat.succ [(«term_+_» («term_*_» (Term.app `Nat.succ [`n]) "*" `m) "+" `n)])))
            "="
            («term_*_» `a "*" `b))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
                [])
               []
               (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.coe_nat_zero)] "]"] [])
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.coe_nat_mul)] "]") [])
               []
               (Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] `Nat.mul_succ)
                  ","
                  (Tactic.simpLemma [] [] `Nat.add_succ)
                  ","
                  (Tactic.simpLemma [] [] `Nat.succ_add)]
                 "]"]
                [])]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt.intro
       [(Term.show
         "show"
         («term_=_»
          («term_+_»
           (num "0")
           "+"
           (coeNotation "↑" (Term.app `Nat.succ [(«term_+_» («term_*_» (Term.app `Nat.succ [`n]) "*" `m) "+" `n)])))
          "="
          («term_*_» `a "*" `b))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
              [])
             []
             (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.coe_nat_zero)] "]"] [])
             []
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.coe_nat_mul)] "]") [])
             []
             (Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `Nat.mul_succ)
                ","
                (Tactic.simpLemma [] [] `Nat.add_succ)
                ","
                (Tactic.simpLemma [] [] `Nat.succ_add)]
               "]"]
              [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        («term_+_»
         (num "0")
         "+"
         (coeNotation "↑" (Term.app `Nat.succ [(«term_+_» («term_*_» (Term.app `Nat.succ [`n]) "*" `m) "+" `n)])))
        "="
        («term_*_» `a "*" `b))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hn) "," (Tactic.rwRule ["←"] `hm)] "]")
            [])
           []
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Int.coe_nat_zero)] "]"] [])
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.coe_nat_mul)] "]") [])
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `Nat.mul_succ)
              ","
              (Tactic.simpLemma [] [] `Nat.add_succ)
              ","
              (Tactic.simpLemma [] [] `Nat.succ_add)]
             "]"]
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `Nat.mul_succ)
         ","
         (Tactic.simpLemma [] [] `Nat.add_succ)
         ","
         (Tactic.simpLemma [] [] `Nat.succ_add)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.succ_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.add_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.mul_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Int.coe_nat_mul)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_nat_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
    mul_pos
    { a b : ℤ } ( ha : 0 < a ) ( hb : 0 < b ) : 0 < a * b
    :=
      lt.elim
        ha
          fun
            n
              =>
              fun
                hn
                  =>
                  lt.elim
                    hb
                      fun
                        m
                          =>
                          fun
                            hm
                              =>
                              lt.intro
                                show
                                  0 + ↑ Nat.succ Nat.succ n * m + n = a * b
                                  by
                                    rw [ ← hn , ← hm ]
                                      simp [ Int.coe_nat_zero ]
                                      rw [ ← Int.coe_nat_mul ]
                                      simp [ Nat.mul_succ , Nat.add_succ , Nat.succ_add ]

protected theorem zero_lt_one : (0 : ℤ) < 1 :=
  trivial

protected theorem lt_iff_le_not_le {a b : ℤ} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  simp [Int.lt_iff_le_and_ne]
  constructor <;> intro h
  · cases' h with hab hn
    constructor
    · assumption
      
    · intro hba
      simp [Int.le_antisymm hab hba] at *
      contradiction
      
    
  · cases' h with hab hn
    constructor
    · assumption
      
    · intro h
      simp_all
      
    

instance : LinearOrder Int where
  le := Int.le
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt := Int.lt
  lt_iff_le_not_le := @Int.lt_iff_le_not_le
  le_total := Int.le_total
  DecidableEq := Int.decidableEq
  decidableLe := Int.decidableLe
  decidableLt := Int.decidableLt

theorem eq_nat_abs_of_zero_le {a : ℤ} (h : 0 ≤ a) : a = natAbs a := by
  let ⟨n, e⟩ := eq_coe_of_zero_le h
  rw [e] <;> rfl

theorem le_nat_abs {a : ℤ} : a ≤ natAbs a :=
  Or.elim (le_total 0 a) (fun h => by rw [eq_nat_abs_of_zero_le h] <;> rfl) fun h => le_trans h (coe_zero_le _)

theorem neg_succ_lt_zero (n : ℕ) : -[1 + n] < 0 :=
  lt_of_not_ge fun h => by
    let ⟨m, h⟩ := eq_coe_of_zero_le h
    contradiction

theorem eq_neg_succ_of_lt_zero : ∀ {a : ℤ}, a < 0 → ∃ n : ℕ, a = -[1 + n]
  | (n : ℕ), h => absurd h (not_lt_of_ge (coe_zero_le _))
  | -[1 + n], h => ⟨n, rfl⟩

-- int is an ordered add comm group
protected theorem eq_neg_of_eq_neg {a b : ℤ} (h : a = -b) : b = -a := by rw [h, Int.neg_neg]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_add_cancel_left [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b] [":" (Int.termℤ "ℤ")] [] ")")]
       (Term.typeSpec ":" («term_=_» («term_+_» («term-_» "-" `a) "+" («term_+_» `a "+" `b)) "=" `b)))
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
              (Tactic.rwRule [] `Int.add_left_neg)
              ","
              (Tactic.rwRule [] `Int.zero_add)]
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
             (Tactic.rwRule [] `Int.add_left_neg)
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
        [(Tactic.rwRule ["←"] `Int.add_assoc)
         ","
         (Tactic.rwRule [] `Int.add_left_neg)
         ","
         (Tactic.rwRule [] `Int.zero_add)]
        "]")
       [])
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
    neg_add_cancel_left
    ( a b : ℤ ) : - a + a + b = b
    := by rw [ ← Int.add_assoc , Int.add_left_neg , Int.zero_add ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_neg_cancel_left [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b] [":" (Int.termℤ "ℤ")] [] ")")]
       (Term.typeSpec ":" («term_=_» («term_+_» `a "+" («term_+_» («term-_» "-" `a) "+" `b)) "=" `b)))
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
              (Tactic.rwRule [] `Int.add_right_neg)
              ","
              (Tactic.rwRule [] `Int.zero_add)]
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
        [(Tactic.rwRule ["←"] `Int.add_assoc)
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
    add_neg_cancel_left
    ( a b : ℤ ) : a + - a + b = b
    := by rw [ ← Int.add_assoc , Int.add_right_neg , Int.zero_add ]

protected theorem add_neg_cancel_right (a b : ℤ) : a + b + -b = a := by
  rw [Int.add_assoc, Int.add_right_neg, Int.add_zero]

protected theorem neg_add_cancel_right (a b : ℤ) : a + -b + b = a := by
  rw [Int.add_assoc, Int.add_left_neg, Int.add_zero]

protected theorem sub_self (a : ℤ) : a - a = 0 := by rw [Int.sub_eq_add_neg, Int.add_right_neg]

protected theorem sub_eq_zero_of_eq {a b : ℤ} (h : a = b) : a - b = 0 := by rw [h, Int.sub_self]

protected theorem eq_of_sub_eq_zero {a b : ℤ} (h : a - b = 0) : a = b := by
  have : 0 + b = b := by rw [Int.zero_add]
  have : a - b + b = b := by rwa [h]
  rwa [Int.sub_eq_add_neg, Int.neg_add_cancel_right] at this

protected theorem sub_eq_zero_iff_eq {a b : ℤ} : a - b = 0 ↔ a = b :=
  ⟨Int.eq_of_sub_eq_zero, Int.sub_eq_zero_of_eq⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_eq_of_add_eq_zero [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_=_» («term_+_» `a "+" `b) "=" (num "0"))] [] ")")]
       (Term.typeSpec ":" («term_=_» («term-_» "-" `a) "=" `b)))
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
             [(Tactic.rwRule ["←"] (Term.app `Int.add_zero [(«term-_» "-" `a)]))
              ","
              (Tactic.rwRule ["←"] `h)
              ","
              (Tactic.rwRule ["←"] `Int.add_assoc)
              ","
              (Tactic.rwRule [] `Int.add_left_neg)
              ","
              (Tactic.rwRule [] `Int.zero_add)]
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
            [(Tactic.rwRule ["←"] (Term.app `Int.add_zero [(«term-_» "-" `a)]))
             ","
             (Tactic.rwRule ["←"] `h)
             ","
             (Tactic.rwRule ["←"] `Int.add_assoc)
             ","
             (Tactic.rwRule [] `Int.add_left_neg)
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
        [(Tactic.rwRule ["←"] (Term.app `Int.add_zero [(«term-_» "-" `a)]))
         ","
         (Tactic.rwRule ["←"] `h)
         ","
         (Tactic.rwRule ["←"] `Int.add_assoc)
         ","
         (Tactic.rwRule [] `Int.add_left_neg)
         ","
         (Tactic.rwRule [] `Int.zero_add)]
        "]")
       [])
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
@[ simp ] protected
  theorem
    neg_eq_of_add_eq_zero
    { a b : ℤ } ( h : a + b = 0 ) : - a = b
    := by rw [ ← Int.add_zero - a , ← h , ← Int.add_assoc , Int.add_left_neg , Int.zero_add ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_mul_eq_neg_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b] [":" (Int.termℤ "ℤ")] [] ")")]
       (Term.typeSpec ":" («term_=_» («term-_» "-" («term_*_» `a "*" `b)) "=" («term_*_» («term-_» "-" `a) "*" `b))))
      (Command.declValSimple
       ":="
       (Term.app
        `Int.neg_eq_of_add_eq_zero
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] `Int.distrib_right)
                ","
                (Tactic.rwRule [] `Int.add_right_neg)
                ","
                (Tactic.rwRule [] `Int.zero_mul)]
               "]")
              [])])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Int.neg_eq_of_add_eq_zero
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `Int.distrib_right)
               ","
               (Tactic.rwRule [] `Int.add_right_neg)
               ","
               (Tactic.rwRule [] `Int.zero_mul)]
              "]")
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
            [(Tactic.rwRule ["←"] `Int.distrib_right)
             ","
             (Tactic.rwRule [] `Int.add_right_neg)
             ","
             (Tactic.rwRule [] `Int.zero_mul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `Int.distrib_right)
         ","
         (Tactic.rwRule [] `Int.add_right_neg)
         ","
         (Tactic.rwRule [] `Int.zero_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.zero_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_right_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.distrib_right
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
    neg_mul_eq_neg_mul
    ( a b : ℤ ) : - a * b = - a * b
    := Int.neg_eq_of_add_eq_zero by rw [ ← Int.distrib_right , Int.add_right_neg , Int.zero_mul ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_mul_eq_mul_neg [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b] [":" (Int.termℤ "ℤ")] [] ")")]
       (Term.typeSpec ":" («term_=_» («term-_» "-" («term_*_» `a "*" `b)) "=" («term_*_» `a "*" («term-_» "-" `b)))))
      (Command.declValSimple
       ":="
       (Term.app
        `Int.neg_eq_of_add_eq_zero
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] `Int.distrib_left)
                ","
                (Tactic.rwRule [] `Int.add_right_neg)
                ","
                (Tactic.rwRule [] `Int.mul_zero)]
               "]")
              [])])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Int.neg_eq_of_add_eq_zero
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `Int.distrib_left)
               ","
               (Tactic.rwRule [] `Int.add_right_neg)
               ","
               (Tactic.rwRule [] `Int.mul_zero)]
              "]")
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
            [(Tactic.rwRule ["←"] `Int.distrib_left)
             ","
             (Tactic.rwRule [] `Int.add_right_neg)
             ","
             (Tactic.rwRule [] `Int.mul_zero)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `Int.distrib_left)
         ","
         (Tactic.rwRule [] `Int.add_right_neg)
         ","
         (Tactic.rwRule [] `Int.mul_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_right_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.distrib_left
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
    neg_mul_eq_mul_neg
    ( a b : ℤ ) : - a * b = a * - b
    := Int.neg_eq_of_add_eq_zero by rw [ ← Int.distrib_left , Int.add_right_neg , Int.mul_zero ]

theorem neg_mul_eq_neg_mul_symm (a b : ℤ) : -a * b = -(a * b) :=
  Eq.symm (Int.neg_mul_eq_neg_mul a b)

theorem mul_neg_eq_neg_mul_symm (a b : ℤ) : a * -b = -(a * b) :=
  Eq.symm (Int.neg_mul_eq_mul_neg a b)

attribute [local simp] neg_mul_eq_neg_mul_symm mul_neg_eq_neg_mul_symm

protected theorem neg_mul_neg (a b : ℤ) : -a * -b = a * b := by simp

protected theorem neg_mul_comm (a b : ℤ) : -a * b = a * -b := by simp

protected theorem mul_sub (a b c : ℤ) : a * (b - c) = a * b - a * c :=
  calc
    a * (b - c) = a * b + a * -c := Int.distrib_left a b (-c)
    _ = a * b - a * c := by simp
    

protected theorem sub_mul (a b c : ℤ) : (a - b) * c = a * c - b * c :=
  calc
    (a - b) * c = a * c + -b * c := Int.distrib_right a (-b) c
    _ = a * c - b * c := by simp
    

section

protected theorem le_of_add_le_add_left {a b c : ℤ} (h : a + b ≤ a + c) : b ≤ c := by
  have : -a + (a + b) ≤ -a + (a + c) := Int.add_le_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption

protected theorem lt_of_add_lt_add_left {a b c : ℤ} (h : a + b < a + c) : b < c := by
  have : -a + (a + b) < -a + (a + c) := Int.add_lt_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption

protected theorem add_le_add_right {a b : ℤ} (h : a ≤ b) (c : ℤ) : a + c ≤ b + c :=
  Int.add_comm c a ▸ Int.add_comm c b ▸ Int.add_le_add_left h c

protected theorem add_lt_add_right {a b : ℤ} (h : a < b) (c : ℤ) : a + c < b + c := by
  rw [Int.add_comm a c, Int.add_comm b c]
  exact Int.add_lt_add_left h c

protected theorem add_le_add {a b c d : ℤ} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  le_trans (Int.add_le_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected theorem le_add_of_nonneg_right {a b : ℤ} (h : 0 ≤ b) : a ≤ a + b := by
  have : a + b ≥ a + 0 := Int.add_le_add_left h a
  rwa [Int.add_zero] at this

protected theorem le_add_of_nonneg_left {a b : ℤ} (h : 0 ≤ b) : a ≤ b + a := by
  have : 0 + a ≤ b + a := Int.add_le_add_right h a
  rwa [Int.zero_add] at this

protected theorem add_lt_add {a b c d : ℤ} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  lt_trans (Int.add_lt_add_right h₁ c) (Int.add_lt_add_left h₂ b)

protected theorem add_lt_add_of_le_of_lt {a b c d : ℤ} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
  lt_of_le_of_lt (Int.add_le_add_right h₁ c) (Int.add_lt_add_left h₂ b)

protected theorem add_lt_add_of_lt_of_le {a b c d : ℤ} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (Int.add_lt_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected theorem lt_add_of_pos_right (a : ℤ) {b : ℤ} (h : 0 < b) : a < a + b := by
  have : a + 0 < a + b := Int.add_lt_add_left h a
  rwa [Int.add_zero] at this

protected theorem lt_add_of_pos_left (a : ℤ) {b : ℤ} (h : 0 < b) : a < b + a := by
  have : 0 + a < b + a := Int.add_lt_add_right h a
  rwa [Int.zero_add] at this

protected theorem le_of_add_le_add_right {a b c : ℤ} (h : a + b ≤ c + b) : a ≤ c :=
  Int.le_of_add_le_add_left
    (show b + a ≤ b + c by
      rw [Int.add_comm b a, Int.add_comm b c]
      assumption)

protected theorem lt_of_add_lt_add_right {a b c : ℤ} (h : a + b < c + b) : a < c :=
  Int.lt_of_add_lt_add_left
    (show b + a < b + c by
      rw [Int.add_comm b a, Int.add_comm b c]
      assumption)

-- here we start using properties of zero.
protected theorem add_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_le_add ha hb

protected theorem add_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add ha hb

protected theorem add_pos_of_pos_of_nonneg {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_lt_of_le ha hb

protected theorem add_pos_of_nonneg_of_pos {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_le_of_lt ha hb

protected theorem add_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_le_add ha hb

protected theorem add_neg {a b : ℤ} (ha : a < 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add ha hb

protected theorem add_neg_of_neg_of_nonpos {a b : ℤ} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_lt_of_le ha hb

protected theorem add_neg_of_nonpos_of_neg {a b : ℤ} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
  Int.zero_add (0 : ℤ) ▸ Int.add_lt_add_of_le_of_lt ha hb

protected theorem lt_add_of_le_of_pos {a b c : ℤ} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
  Int.add_zero b ▸ Int.add_lt_add_of_le_of_lt hbc ha

protected theorem sub_add_cancel (a b : ℤ) : a - b + b = a :=
  Int.neg_add_cancel_right a b

protected theorem add_sub_cancel (a b : ℤ) : a + b - b = a :=
  Int.add_neg_cancel_right a b

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_sub_assoc [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b `c] [":" (Int.termℤ "ℤ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_» («term_-_» («term_+_» `a "+" `b) "-" `c) "=" («term_+_» `a "+" («term_-_» `b "-" `c)))))
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
             [(Tactic.rwRule [] `Int.sub_eq_add_neg)
              ","
              (Tactic.rwRule [] `Int.add_assoc)
              ","
              (Tactic.rwRule ["←"] `Int.sub_eq_add_neg)]
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
            [(Tactic.rwRule [] `Int.sub_eq_add_neg)
             ","
             (Tactic.rwRule [] `Int.add_assoc)
             ","
             (Tactic.rwRule ["←"] `Int.sub_eq_add_neg)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Int.sub_eq_add_neg)
         ","
         (Tactic.rwRule [] `Int.add_assoc)
         ","
         (Tactic.rwRule ["←"] `Int.sub_eq_add_neg)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.sub_eq_add_neg
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
    add_sub_assoc
    ( a b c : ℤ ) : a + b - c = a + b - c
    := by rw [ Int.sub_eq_add_neg , Int.add_assoc , ← Int.sub_eq_add_neg ]

protected theorem neg_le_neg {a b : ℤ} (h : a ≤ b) : -b ≤ -a := by
  have : 0 ≤ -a + b := Int.add_left_neg a ▸ Int.add_le_add_left h (-a)
  have : 0 + -b ≤ -a + b + -b := Int.add_le_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this

protected theorem le_of_neg_le_neg {a b : ℤ} (h : -b ≤ -a) : a ≤ b :=
  suffices - -a ≤ - -b by
    simp [Int.neg_neg] at this
    assumption
  Int.neg_le_neg h

protected theorem nonneg_of_neg_nonpos {a : ℤ} (h : -a ≤ 0) : 0 ≤ a :=
  have : -a ≤ -0 := by rwa [Int.neg_zero]
  Int.le_of_neg_le_neg this

protected theorem neg_nonpos_of_nonneg {a : ℤ} (h : 0 ≤ a) : -a ≤ 0 := by
  have : -a ≤ -0 := Int.neg_le_neg h
  rwa [Int.neg_zero] at this

protected theorem nonpos_of_neg_nonneg {a : ℤ} (h : 0 ≤ -a) : a ≤ 0 :=
  have : -0 ≤ -a := by rwa [Int.neg_zero]
  Int.le_of_neg_le_neg this

protected theorem neg_nonneg_of_nonpos {a : ℤ} (h : a ≤ 0) : 0 ≤ -a := by
  have : -0 ≤ -a := Int.neg_le_neg h
  rwa [Int.neg_zero] at this

protected theorem neg_lt_neg {a b : ℤ} (h : a < b) : -b < -a := by
  have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_left h (-a)
  have : 0 + -b < -a + b + -b := Int.add_lt_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this

protected theorem lt_of_neg_lt_neg {a b : ℤ} (h : -b < -a) : a < b :=
  Int.neg_neg a ▸ Int.neg_neg b ▸ Int.neg_lt_neg h

protected theorem pos_of_neg_neg {a : ℤ} (h : -a < 0) : 0 < a :=
  have : -a < -0 := by rwa [Int.neg_zero]
  Int.lt_of_neg_lt_neg this

protected theorem neg_neg_of_pos {a : ℤ} (h : 0 < a) : -a < 0 := by
  have : -a < -0 := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this

protected theorem neg_of_neg_pos {a : ℤ} (h : 0 < -a) : a < 0 :=
  have : -0 < -a := by rwa [Int.neg_zero]
  Int.lt_of_neg_lt_neg this

protected theorem neg_pos_of_neg {a : ℤ} (h : a < 0) : 0 < -a := by
  have : -0 < -a := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this

protected theorem le_neg_of_le_neg {a b : ℤ} (h : a ≤ -b) : b ≤ -a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h

protected theorem neg_le_of_neg_le {a b : ℤ} (h : -a ≤ b) : -b ≤ a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h

protected theorem lt_neg_of_lt_neg {a b : ℤ} (h : a < -b) : b < -a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h

protected theorem neg_lt_of_neg_lt {a b : ℤ} (h : -a < b) : -b < a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h

protected theorem sub_nonneg_of_le {a b : ℤ} (h : b ≤ a) : 0 ≤ a - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem le_of_sub_nonneg {a b : ℤ} (h : 0 ≤ a - b) : b ≤ a := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_nonpos_of_le {a b : ℤ} (h : a ≤ b) : a - b ≤ 0 := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem le_of_sub_nonpos {a b : ℤ} (h : a - b ≤ 0) : a ≤ b := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_pos_of_lt {a b : ℤ} (h : b < a) : 0 < a - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem lt_of_sub_pos {a b : ℤ} (h : 0 < a - b) : b < a := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_neg_of_lt {a b : ℤ} (h : a < b) : a - b < 0 := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem lt_of_sub_neg {a b : ℤ} (h : a - b < 0) : a < b := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem add_le_of_le_neg_add {a b c : ℤ} (h : b ≤ -a + c) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [Int.add_neg_cancel_left] at h

protected theorem le_neg_add_of_add_le {a b c : ℤ} (h : a + b ≤ c) : b ≤ -a + c := by
  have h := Int.add_le_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_le_of_le_sub_left [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b `c] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `b "≤" («term_-_» `c "-" `a))] [] ")")]
       (Term.typeSpec ":" («term_≤_» («term_+_» `a "+" `b) "≤" `c)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `Int.add_le_add_left [`h `a]))))
           []
           (tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule ["←"] `Int.add_sub_assoc)
              ","
              (Tactic.rwRule [] (Term.app `Int.add_comm [`a `c]))
              ","
              (Tactic.rwRule [] `Int.add_sub_cancel)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])])))
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
           (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `Int.add_le_add_left [`h `a]))))
          []
          (tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `Int.add_sub_assoc)
             ","
             (Tactic.rwRule [] (Term.app `Int.add_comm [`a `c]))
             ","
             (Tactic.rwRule [] `Int.add_sub_cancel)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `Int.add_sub_assoc)
         ","
         (Tactic.rwRule [] (Term.app `Int.add_comm [`a `c]))
         ","
         (Tactic.rwRule [] `Int.add_sub_cancel)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_sub_cancel
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.add_comm [`a `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_sub_assoc
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
    add_le_of_le_sub_left
    { a b c : ℤ } ( h : b ≤ c - a ) : a + b ≤ c
    := by have h := Int.add_le_add_left h a rwa [ ← Int.add_sub_assoc , Int.add_comm a c , Int.add_sub_cancel ] at h

protected theorem le_sub_left_of_add_le {a b c : ℤ} (h : a + b ≤ c) : b ≤ c - a := by
  have h := Int.add_le_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected theorem add_le_of_le_sub_right {a b c : ℤ} (h : a ≤ c - b) : a + b ≤ c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel] at h

protected theorem le_sub_right_of_add_le {a b c : ℤ} (h : a + b ≤ c) : a ≤ c - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected theorem le_add_of_neg_add_le {a b c : ℤ} (h : -b + a ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_left h b
  rwa [Int.add_neg_cancel_left] at h

protected theorem neg_add_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -b + a ≤ c := by
  have h := Int.add_le_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected theorem le_add_of_sub_left_le {a b c : ℤ} (h : a - b ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected theorem sub_left_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : a - b ≤ c := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected theorem le_add_of_sub_right_le {a b c : ℤ} (h : a - c ≤ b) : a ≤ b + c := by
  have h := Int.add_le_add_right h c
  rwa [Int.sub_add_cancel] at h

protected theorem sub_right_le_of_le_add {a b c : ℤ} (h : a ≤ b + c) : a - c ≤ b := by
  have h := Int.add_le_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected theorem le_add_of_neg_add_le_left {a b c : ℤ} (h : -b + a ≤ c) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_left_le h

protected theorem neg_add_le_left_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -b + a ≤ c := by
  rw [Int.add_comm]
  exact Int.sub_left_le_of_le_add h

protected theorem le_add_of_neg_add_le_right {a b c : ℤ} (h : -c + a ≤ b) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_right_le h

protected theorem neg_add_le_right_of_le_add {a b c : ℤ} (h : a ≤ b + c) : -c + a ≤ b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_le_left_of_le_add h

protected theorem le_add_of_neg_le_sub_left {a b c : ℤ} (h : -a ≤ b - c) : c ≤ a + b :=
  Int.le_add_of_neg_add_le_left (Int.add_le_of_le_sub_right h)

protected theorem neg_le_sub_left_of_le_add {a b c : ℤ} (h : c ≤ a + b) : -a ≤ b - c := by
  have h := Int.le_neg_add_of_add_le (Int.sub_left_le_of_le_add h)
  rwa [Int.add_comm] at h

protected theorem le_add_of_neg_le_sub_right {a b c : ℤ} (h : -b ≤ a - c) : c ≤ a + b :=
  Int.le_add_of_sub_right_le (Int.add_le_of_le_sub_left h)

protected theorem neg_le_sub_right_of_le_add {a b c : ℤ} (h : c ≤ a + b) : -b ≤ a - c :=
  Int.le_sub_left_of_add_le (Int.sub_right_le_of_le_add h)

protected theorem sub_le_of_sub_le {a b c : ℤ} (h : a - b ≤ c) : a - c ≤ b :=
  Int.sub_left_le_of_le_add (Int.le_add_of_sub_right_le h)

protected theorem sub_le_sub_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c - b ≤ c - a :=
  Int.add_le_add_left (Int.neg_le_neg h) c

protected theorem sub_le_sub_right {a b : ℤ} (h : a ≤ b) (c : ℤ) : a - c ≤ b - c :=
  Int.add_le_add_right h (-c)

protected theorem sub_le_sub {a b c d : ℤ} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  Int.add_le_add hab (Int.neg_le_neg hcd)

protected theorem add_lt_of_lt_neg_add {a b c : ℤ} (h : b < -a + c) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [Int.add_neg_cancel_left] at h

protected theorem lt_neg_add_of_add_lt {a b c : ℤ} (h : a + b < c) : b < -a + c := by
  have h := Int.add_lt_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_lt_of_lt_sub_left [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b `c] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_<_» `b "<" («term_-_» `c "-" `a))] [] ")")]
       (Term.typeSpec ":" («term_<_» («term_+_» `a "+" `b) "<" `c)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `Int.add_lt_add_left [`h `a]))))
           []
           (tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule ["←"] `Int.add_sub_assoc)
              ","
              (Tactic.rwRule [] (Term.app `Int.add_comm [`a `c]))
              ","
              (Tactic.rwRule [] `Int.add_sub_cancel)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])])))
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
           (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `Int.add_lt_add_left [`h `a]))))
          []
          (tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `Int.add_sub_assoc)
             ","
             (Tactic.rwRule [] (Term.app `Int.add_comm [`a `c]))
             ","
             (Tactic.rwRule [] `Int.add_sub_cancel)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `Int.add_sub_assoc)
         ","
         (Tactic.rwRule [] (Term.app `Int.add_comm [`a `c]))
         ","
         (Tactic.rwRule [] `Int.add_sub_cancel)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_sub_cancel
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.add_comm [`a `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.add_sub_assoc
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
    add_lt_of_lt_sub_left
    { a b c : ℤ } ( h : b < c - a ) : a + b < c
    := by have h := Int.add_lt_add_left h a rwa [ ← Int.add_sub_assoc , Int.add_comm a c , Int.add_sub_cancel ] at h

protected theorem lt_sub_left_of_add_lt {a b c : ℤ} (h : a + b < c) : b < c - a := by
  have h := Int.add_lt_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h

protected theorem add_lt_of_lt_sub_right {a b c : ℤ} (h : a < c - b) : a + b < c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel] at h

protected theorem lt_sub_right_of_add_lt {a b c : ℤ} (h : a + b < c) : a < c - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h

protected theorem lt_add_of_neg_add_lt {a b c : ℤ} (h : -b + a < c) : a < b + c := by
  have h := Int.add_lt_add_left h b
  rwa [Int.add_neg_cancel_left] at h

protected theorem neg_add_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : -b + a < c := by
  have h := Int.add_lt_add_left h (-b)
  rwa [Int.neg_add_cancel_left] at h

protected theorem lt_add_of_sub_left_lt {a b c : ℤ} (h : a - b < c) : a < b + c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.add_comm] at h

protected theorem sub_left_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : a - b < c := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected theorem lt_add_of_sub_right_lt {a b c : ℤ} (h : a - c < b) : a < b + c := by
  have h := Int.add_lt_add_right h c
  rwa [Int.sub_add_cancel] at h

protected theorem sub_right_lt_of_lt_add {a b c : ℤ} (h : a < b + c) : a - c < b := by
  have h := Int.add_lt_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h

protected theorem lt_add_of_neg_add_lt_left {a b c : ℤ} (h : -b + a < c) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_left_lt h

protected theorem neg_add_lt_left_of_lt_add {a b c : ℤ} (h : a < b + c) : -b + a < c := by
  rw [Int.add_comm]
  exact Int.sub_left_lt_of_lt_add h

protected theorem lt_add_of_neg_add_lt_right {a b c : ℤ} (h : -c + a < b) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_right_lt h

protected theorem neg_add_lt_right_of_lt_add {a b c : ℤ} (h : a < b + c) : -c + a < b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_lt_left_of_lt_add h

protected theorem lt_add_of_neg_lt_sub_left {a b c : ℤ} (h : -a < b - c) : c < a + b :=
  Int.lt_add_of_neg_add_lt_left (Int.add_lt_of_lt_sub_right h)

protected theorem neg_lt_sub_left_of_lt_add {a b c : ℤ} (h : c < a + b) : -a < b - c := by
  have h := Int.lt_neg_add_of_add_lt (Int.sub_left_lt_of_lt_add h)
  rwa [Int.add_comm] at h

protected theorem lt_add_of_neg_lt_sub_right {a b c : ℤ} (h : -b < a - c) : c < a + b :=
  Int.lt_add_of_sub_right_lt (Int.add_lt_of_lt_sub_left h)

protected theorem neg_lt_sub_right_of_lt_add {a b c : ℤ} (h : c < a + b) : -b < a - c :=
  Int.lt_sub_left_of_add_lt (Int.sub_right_lt_of_lt_add h)

protected theorem sub_lt_of_sub_lt {a b c : ℤ} (h : a - b < c) : a - c < b :=
  Int.sub_left_lt_of_lt_add (Int.lt_add_of_sub_right_lt h)

protected theorem sub_lt_sub_left {a b : ℤ} (h : a < b) (c : ℤ) : c - b < c - a :=
  Int.add_lt_add_left (Int.neg_lt_neg h) c

protected theorem sub_lt_sub_right {a b : ℤ} (h : a < b) (c : ℤ) : a - c < b - c :=
  Int.add_lt_add_right h (-c)

protected theorem sub_lt_sub {a b c d : ℤ} (hab : a < b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_add hab (Int.neg_lt_neg hcd)

protected theorem sub_lt_sub_of_le_of_lt {a b c d : ℤ} (hab : a ≤ b) (hcd : c < d) : a - d < b - c :=
  Int.add_lt_add_of_le_of_lt hab (Int.neg_lt_neg hcd)

protected theorem sub_lt_sub_of_lt_of_le {a b c d : ℤ} (hab : a < b) (hcd : c ≤ d) : a - d < b - c :=
  Int.add_lt_add_of_lt_of_le hab (Int.neg_le_neg hcd)

protected theorem sub_le_self (a : ℤ) {b : ℤ} (h : 0 ≤ b) : a - b ≤ a :=
  calc
    a - b = a + -b := rfl
    _ ≤ a + 0 := Int.add_le_add_left (Int.neg_nonpos_of_nonneg h) _
    _ = a := by rw [Int.add_zero]
    

protected theorem sub_lt_self (a : ℤ) {b : ℤ} (h : 0 < b) : a - b < a :=
  calc
    a - b = a + -b := rfl
    _ < a + 0 := Int.add_lt_add_left (Int.neg_neg_of_pos h) _
    _ = a := by rw [Int.add_zero]
    

protected theorem add_le_add_three {a b c d e f : ℤ} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a + b + c ≤ d + e + f :=
  by
  apply le_trans
  apply Int.add_le_add
  apply Int.add_le_add
  assumption'
  apply le_refl

end

-- missing facts
protected theorem mul_lt_mul_of_pos_left {a b c : ℤ} (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b := by
  have : 0 < b - a := Int.sub_pos_of_lt h₁
  have : 0 < c * (b - a) := Int.mul_pos h₂ this
  rw [Int.mul_sub] at this
  exact Int.lt_of_sub_pos this

protected theorem mul_lt_mul_of_pos_right {a b c : ℤ} (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c := by
  have : 0 < b - a := Int.sub_pos_of_lt h₁
  have : 0 < (b - a) * c := Int.mul_pos this h₂
  rw [Int.sub_mul] at this
  exact Int.lt_of_sub_pos this

protected theorem mul_le_mul_of_nonneg_left {a b c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b := by
  by_cases hba:b ≤ a
  · simp [le_antisymm hba h₁]
    
  by_cases hc0:c ≤ 0
  · simp [le_antisymm hc0 h₂, Int.zero_mul]
    
  exact (le_not_le_of_lt (Int.mul_lt_mul_of_pos_left (lt_of_le_not_le h₁ hba) (lt_of_le_not_le h₂ hc0))).left

protected theorem mul_le_mul_of_nonneg_right {a b c : ℤ} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c := by
  by_cases hba:b ≤ a
  · simp [le_antisymm hba h₁]
    
  by_cases hc0:c ≤ 0
  · simp [le_antisymm hc0 h₂, Int.mul_zero]
    
  exact (le_not_le_of_lt (Int.mul_lt_mul_of_pos_right (lt_of_le_not_le h₁ hba) (lt_of_le_not_le h₂ hc0))).left

-- TODO: there are four variations, depending on which variables we assume to be nonneg
protected theorem mul_le_mul {a b c d : ℤ} (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d :=
  calc
    a * b ≤ c * b := Int.mul_le_mul_of_nonneg_right hac nn_b
    _ ≤ c * d := Int.mul_le_mul_of_nonneg_left hbd nn_c
    

protected theorem mul_nonpos_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  have h : a * b ≤ a * 0 := Int.mul_le_mul_of_nonneg_left hb ha
  rwa [Int.mul_zero] at h

protected theorem mul_nonpos_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  have h : a * b ≤ 0 * b := Int.mul_le_mul_of_nonneg_right ha hb
  rwa [Int.zero_mul] at h

protected theorem mul_lt_mul {a b c d : ℤ} (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b) (nn_c : 0 ≤ c) : a * b < c * d :=
  calc
    a * b < c * b := Int.mul_lt_mul_of_pos_right hac pos_b
    _ ≤ c * d := Int.mul_le_mul_of_nonneg_left hbd nn_c
    

protected theorem mul_lt_mul' {a b c d : ℤ} (h1 : a ≤ c) (h2 : b < d) (h3 : 0 ≤ b) (h4 : 0 < c) : a * b < c * d :=
  calc
    a * b ≤ c * b := Int.mul_le_mul_of_nonneg_right h1 h3
    _ < c * d := Int.mul_lt_mul_of_pos_left h2 h4
    

protected theorem mul_neg_of_pos_of_neg {a b : ℤ} (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  have h : a * b < a * 0 := Int.mul_lt_mul_of_pos_left hb ha
  rwa [Int.mul_zero] at h

protected theorem mul_neg_of_neg_of_pos {a b : ℤ} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have h : a * b < 0 * b := Int.mul_lt_mul_of_pos_right ha hb
  rwa [Int.zero_mul] at h

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_le_mul_of_nonpos_right [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b `c] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `b "≤" `a)] [] ")")
        (Term.explicitBinder "(" [`hc] [":" («term_≤_» `c "≤" (num "0"))] [] ")")]
       (Term.typeSpec ":" («term_≤_» («term_*_» `a "*" `c) "≤" («term_*_» `b "*" `c))))
      (Command.declValSimple
       ":="
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_≥_» («term-_» "-" `c) "≥" (num "0")))]
          ":="
          (Term.app `Int.neg_nonneg_of_nonpos [`hc])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_≤_» («term_*_» `b "*" («term-_» "-" `c)) "≤" («term_*_» `a "*" («term-_» "-" `c))))]
           ":="
           (Term.app `Int.mul_le_mul_of_nonneg_right [`h `this])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              («term_≤_» («term-_» "-" («term_*_» `b "*" `c)) "≤" («term-_» "-" («term_*_» `a "*" `c))))]
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
          []
          (Term.app `Int.le_of_neg_le_neg [`this]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_≥_» («term-_» "-" `c) "≥" (num "0")))]
         ":="
         (Term.app `Int.neg_nonneg_of_nonpos [`hc])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_≤_» («term_*_» `b "*" («term-_» "-" `c)) "≤" («term_*_» `a "*" («term-_» "-" `c))))]
          ":="
          (Term.app `Int.mul_le_mul_of_nonneg_right [`h `this])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_≤_» («term-_» "-" («term_*_» `b "*" `c)) "≤" («term-_» "-" («term_*_» `a "*" `c))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
         []
         (Term.app `Int.le_of_neg_le_neg [`this]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_≤_» («term_*_» `b "*" («term-_» "-" `c)) "≤" («term_*_» `a "*" («term-_» "-" `c))))]
         ":="
         (Term.app `Int.mul_le_mul_of_nonneg_right [`h `this])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_≤_» («term-_» "-" («term_*_» `b "*" `c)) "≤" («term-_» "-" («term_*_» `a "*" `c))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
        []
        (Term.app `Int.le_of_neg_le_neg [`this])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_≤_» («term-_» "-" («term_*_» `b "*" `c)) "≤" («term-_» "-" («term_*_» `a "*" `c))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
       []
       (Term.app `Int.le_of_neg_le_neg [`this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.le_of_neg_le_neg [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.le_of_neg_le_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.neg_mul_eq_mul_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
    mul_le_mul_of_nonpos_right
    { a b c : ℤ } ( h : b ≤ a ) ( hc : c ≤ 0 ) : a * c ≤ b * c
    :=
      have
        : - c ≥ 0 := Int.neg_nonneg_of_nonpos hc
        have
          : b * - c ≤ a * - c := Int.mul_le_mul_of_nonneg_right h this
          have
            : - b * c ≤ - a * c := by rwa [ ← Int.neg_mul_eq_mul_neg , ← Int.neg_mul_eq_mul_neg ] at this
            Int.le_of_neg_le_neg this

protected theorem mul_nonneg_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  have : 0 * b ≤ a * b := Int.mul_le_mul_of_nonpos_right ha hb
  rwa [Int.zero_mul] at this

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_lt_mul_of_neg_left [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b `c] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_<_» `b "<" `a)] [] ")")
        (Term.explicitBinder "(" [`hc] [":" («term_<_» `c "<" (num "0"))] [] ")")]
       (Term.typeSpec ":" («term_<_» («term_*_» `c "*" `a) "<" («term_*_» `c "*" `b))))
      (Command.declValSimple
       ":="
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_>_» («term-_» "-" `c) ">" (num "0")))]
          ":="
          (Term.app `Int.neg_pos_of_neg [`hc])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_<_» («term_*_» («term-_» "-" `c) "*" `b) "<" («term_*_» («term-_» "-" `c) "*" `a)))]
           ":="
           (Term.app `Int.mul_lt_mul_of_pos_left [`h `this])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              («term_<_» («term-_» "-" («term_*_» `c "*" `b)) "<" («term-_» "-" («term_*_» `c "*" `a))))]
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
          []
          (Term.app `Int.lt_of_neg_lt_neg [`this]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_>_» («term-_» "-" `c) ">" (num "0")))]
         ":="
         (Term.app `Int.neg_pos_of_neg [`hc])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_<_» («term_*_» («term-_» "-" `c) "*" `b) "<" («term_*_» («term-_» "-" `c) "*" `a)))]
          ":="
          (Term.app `Int.mul_lt_mul_of_pos_left [`h `this])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_<_» («term-_» "-" («term_*_» `c "*" `b)) "<" («term-_» "-" («term_*_» `c "*" `a))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
         []
         (Term.app `Int.lt_of_neg_lt_neg [`this]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_<_» («term_*_» («term-_» "-" `c) "*" `b) "<" («term_*_» («term-_» "-" `c) "*" `a)))]
         ":="
         (Term.app `Int.mul_lt_mul_of_pos_left [`h `this])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_<_» («term-_» "-" («term_*_» `c "*" `b)) "<" («term-_» "-" («term_*_» `c "*" `a))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
        []
        (Term.app `Int.lt_of_neg_lt_neg [`this])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_<_» («term-_» "-" («term_*_» `c "*" `b)) "<" («term-_» "-" («term_*_» `c "*" `a))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
       []
       (Term.app `Int.lt_of_neg_lt_neg [`this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.lt_of_neg_lt_neg [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.lt_of_neg_lt_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_neg_mul)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.neg_mul_eq_neg_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
    mul_lt_mul_of_neg_left
    { a b c : ℤ } ( h : b < a ) ( hc : c < 0 ) : c * a < c * b
    :=
      have
        : - c > 0 := Int.neg_pos_of_neg hc
        have
          : - c * b < - c * a := Int.mul_lt_mul_of_pos_left h this
          have
            : - c * b < - c * a := by rwa [ ← Int.neg_mul_eq_neg_mul , ← Int.neg_mul_eq_neg_mul ] at this
            Int.lt_of_neg_lt_neg this

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_lt_mul_of_neg_right [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b `c] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_<_» `b "<" `a)] [] ")")
        (Term.explicitBinder "(" [`hc] [":" («term_<_» `c "<" (num "0"))] [] ")")]
       (Term.typeSpec ":" («term_<_» («term_*_» `a "*" `c) "<" («term_*_» `b "*" `c))))
      (Command.declValSimple
       ":="
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_>_» («term-_» "-" `c) ">" (num "0")))]
          ":="
          (Term.app `Int.neg_pos_of_neg [`hc])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_<_» («term_*_» `b "*" («term-_» "-" `c)) "<" («term_*_» `a "*" («term-_» "-" `c))))]
           ":="
           (Term.app `Int.mul_lt_mul_of_pos_right [`h `this])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              («term_<_» («term-_» "-" («term_*_» `b "*" `c)) "<" («term-_» "-" («term_*_» `a "*" `c))))]
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
          []
          (Term.app `Int.lt_of_neg_lt_neg [`this]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_>_» («term-_» "-" `c) ">" (num "0")))]
         ":="
         (Term.app `Int.neg_pos_of_neg [`hc])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_<_» («term_*_» `b "*" («term-_» "-" `c)) "<" («term_*_» `a "*" («term-_» "-" `c))))]
          ":="
          (Term.app `Int.mul_lt_mul_of_pos_right [`h `this])))
        []
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_<_» («term-_» "-" («term_*_» `b "*" `c)) "<" («term-_» "-" («term_*_» `a "*" `c))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
         []
         (Term.app `Int.lt_of_neg_lt_neg [`this]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_<_» («term_*_» `b "*" («term-_» "-" `c)) "<" («term_*_» `a "*" («term-_» "-" `c))))]
         ":="
         (Term.app `Int.mul_lt_mul_of_pos_right [`h `this])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_<_» («term-_» "-" («term_*_» `b "*" `c)) "<" («term-_» "-" («term_*_» `a "*" `c))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
        []
        (Term.app `Int.lt_of_neg_lt_neg [`this])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_<_» («term-_» "-" («term_*_» `b "*" `c)) "<" («term-_» "-" («term_*_» `a "*" `c))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))))
       []
       (Term.app `Int.lt_of_neg_lt_neg [`this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.lt_of_neg_lt_neg [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.lt_of_neg_lt_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg) "," (Tactic.rwRule ["←"] `Int.neg_mul_eq_mul_neg)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.neg_mul_eq_mul_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
    mul_lt_mul_of_neg_right
    { a b c : ℤ } ( h : b < a ) ( hc : c < 0 ) : a * c < b * c
    :=
      have
        : - c > 0 := Int.neg_pos_of_neg hc
        have
          : b * - c < a * - c := Int.mul_lt_mul_of_pos_right h this
          have
            : - b * c < - a * c := by rwa [ ← Int.neg_mul_eq_mul_neg , ← Int.neg_mul_eq_mul_neg ] at this
            Int.lt_of_neg_lt_neg this

protected theorem mul_pos_of_neg_of_neg {a b : ℤ} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have : 0 * b < a * b := Int.mul_lt_mul_of_neg_right ha hb
  rwa [Int.zero_mul] at this

protected theorem mul_self_le_mul_self {a b : ℤ} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
  Int.mul_le_mul h2 h2 h1 (le_trans h1 h2)

protected theorem mul_self_lt_mul_self {a b : ℤ} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  Int.mul_lt_mul' (le_of_lt h2) h2 h1 (lt_of_le_of_lt h1 h2)

-- more facts specific to int
theorem of_nat_nonneg (n : ℕ) : 0 ≤ ofNat n :=
  trivial

theorem coe_succ_pos (n : Nat) : 0 < (Nat.succ n : ℤ) :=
  coe_nat_lt_coe_nat_of_lt (Nat.succ_pos _)

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : ∃ n : ℕ, a = -n :=
  let ⟨n, h⟩ := eq_coe_of_zero_le (Int.neg_nonneg_of_nonpos H)
  ⟨n, Int.eq_neg_of_eq_neg h.symm⟩

theorem nat_abs_of_nonneg {a : ℤ} (H : 0 ≤ a) : (natAbs a : ℤ) = a :=
  match a, eq_coe_of_zero_le H with
  | _, ⟨n, rfl⟩ => rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `of_nat_nat_abs_of_nonpos [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" (Int.termℤ "ℤ")] "}")
        (Term.explicitBinder "(" [`H] [":" («term_≤_» `a "≤" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.paren "(" [(Term.app `natAbs [`a]) [(Term.typeAscription ":" (Int.termℤ "ℤ"))]] ")")
         "="
         («term-_» "-" `a))))
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
             [(Tactic.rwRule ["←"] `nat_abs_neg)
              ","
              (Tactic.rwRule [] (Term.app `nat_abs_of_nonneg [(Term.app `Int.neg_nonneg_of_nonpos [`H])]))]
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
            [(Tactic.rwRule ["←"] `nat_abs_neg)
             ","
             (Tactic.rwRule [] (Term.app `nat_abs_of_nonneg [(Term.app `Int.neg_nonneg_of_nonpos [`H])]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `nat_abs_neg)
         ","
         (Tactic.rwRule [] (Term.app `nat_abs_of_nonneg [(Term.app `Int.neg_nonneg_of_nonpos [`H])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nat_abs_of_nonneg [(Term.app `Int.neg_nonneg_of_nonpos [`H])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.neg_nonneg_of_nonpos [`H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.neg_nonneg_of_nonpos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Int.neg_nonneg_of_nonpos [`H]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nat_abs_of_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nat_abs_neg
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
  of_nat_nat_abs_of_nonpos
  { a : ℤ } ( H : a ≤ 0 ) : ( natAbs a : ℤ ) = - a
  := by rw [ ← nat_abs_neg , nat_abs_of_nonneg Int.neg_nonneg_of_nonpos H ]

theorem lt_of_add_one_le {a b : ℤ} (H : a + 1 ≤ b) : a < b :=
  H

theorem add_one_le_of_lt {a b : ℤ} (H : a < b) : a + 1 ≤ b :=
  H

theorem lt_add_one_of_le {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
  Int.add_le_add_right H 1

theorem le_of_lt_add_one {a b : ℤ} (H : a < b + 1) : a ≤ b :=
  Int.le_of_add_le_add_right H

theorem sub_one_lt_of_le {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
  Int.sub_right_lt_of_lt_add <| lt_add_one_of_le H

theorem le_of_sub_one_lt {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
  le_of_lt_add_one <| Int.lt_add_of_sub_right_lt H

theorem le_sub_one_of_lt {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
  Int.le_sub_right_of_add_le H

theorem lt_of_le_sub_one {a b : ℤ} (H : a ≤ b - 1) : a < b :=
  Int.add_le_of_le_sub_right H

theorem sign_of_succ (n : Nat) : sign (Nat.succ n) = 1 :=
  rfl

theorem sign_eq_one_of_pos {a : ℤ} (h : 0 < a) : sign a = 1 :=
  match a, eq_succ_of_zero_lt h with
  | _, ⟨n, rfl⟩ => rfl

theorem sign_eq_neg_one_of_neg {a : ℤ} (h : a < 0) : sign a = -1 :=
  match a, eq_neg_succ_of_lt_zero h with
  | _, ⟨n, rfl⟩ => rfl

theorem eq_zero_of_sign_eq_zero : ∀ {a : ℤ}, sign a = 0 → a = 0
  | 0, _ => rfl

theorem pos_of_sign_eq_one : ∀ {a : ℤ}, sign a = 1 → 0 < a
  | (n + 1 : ℕ), _ => coe_nat_lt_coe_nat_of_lt (Nat.succ_pos _)

theorem neg_of_sign_eq_neg_one : ∀ {a : ℤ}, sign a = -1 → a < 0
  | (n + 1 : ℕ), h => nomatch h
  | 0, h => nomatch h
  | -[1 + n], _ => neg_succ_lt_zero _

theorem sign_eq_one_iff_pos (a : ℤ) : sign a = 1 ↔ 0 < a :=
  ⟨pos_of_sign_eq_one, sign_eq_one_of_pos⟩

theorem sign_eq_neg_one_iff_neg (a : ℤ) : sign a = -1 ↔ a < 0 :=
  ⟨neg_of_sign_eq_neg_one, sign_eq_neg_one_of_neg⟩

theorem sign_eq_zero_iff_zero (a : ℤ) : sign a = 0 ↔ a = 0 :=
  ⟨eq_zero_of_sign_eq_zero, fun h => by rw [h, sign_zero]⟩

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  match lt_trichotomy 0 a with
  | Or.inl hlt₁ =>
    match lt_trichotomy 0 b with
    | Or.inl hlt₂ => by
      have : 0 < a * b := Int.mul_pos hlt₁ hlt₂
      rw [h] at this
      exact absurd this (lt_irrefl _)
    | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
    | Or.inr (Or.inr hgt₂) => by
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
    | Or.inr (Or.inr hgt₂) => by
      have : 0 < a * b := Int.mul_pos_of_neg_of_neg hgt₁ hgt₂
      rw [h] at this
      exact absurd this (lt_irrefl _)

protected theorem eq_of_mul_eq_mul_right {a b c : ℤ} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have : b * a - c * a = 0 := Int.sub_eq_zero_of_eq h
  have : (b - c) * a = 0 := by rw [Int.sub_mul, this]
  have : b - c = 0 := (Int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha
  Int.eq_of_sub_eq_zero this

protected theorem eq_of_mul_eq_mul_left {a b c : ℤ} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have : a * b - a * c = 0 := Int.sub_eq_zero_of_eq h
  have : a * (b - c) = 0 := by rw [Int.mul_sub, this]
  have : b - c = 0 := (Int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha
  Int.eq_of_sub_eq_zero this

theorem eq_one_of_mul_eq_self_left {a b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
  Int.eq_of_mul_eq_mul_right Hpos (by rw [Int.one_mul, H])

theorem eq_one_of_mul_eq_self_right {a b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
  Int.eq_of_mul_eq_mul_left Hpos (by rw [Int.mul_one, H])

end Int

