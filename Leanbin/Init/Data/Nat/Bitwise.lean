/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
prelude
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Meta.WellFoundedTactics

universe u

namespace Nat

def boddDiv2 : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | succ n =>
    match bodd_div2 n with
    | (ff, m) => (true, m)
    | (tt, m) => (false, succ m)

def div2 (n : ℕ) : ℕ :=
  (boddDiv2 n).2

def bodd (n : ℕ) : Bool :=
  (boddDiv2 n).1

@[simp]
theorem bodd_zero : bodd 0 = ff :=
  rfl

theorem bodd_one : bodd 1 = tt :=
  rfl

theorem bodd_two : bodd 2 = ff :=
  rfl

@[simp]
theorem bodd_succ (n : ℕ) : bodd (succ n) = not (bodd n) := by
  unfold bodd bodd_div2 <;> cases bodd_div2 n <;> cases fst <;> rfl

@[simp]
theorem bodd_add (m n : ℕ) : bodd (m + n) = xor (bodd m) (bodd n) := by
  induction' n with n IH
  · simp
    cases bodd m <;> rfl
    
  · simp [add_succ, IH]
    cases bodd m <;> cases bodd n <;> rfl
    

@[simp]
theorem bodd_mul (m n : ℕ) : bodd (m * n) = (bodd m && bodd n) := by
  induction' n with n IH
  · simp
    cases bodd m <;> rfl
    
  · simp [mul_succ, IH]
    cases bodd m <;> cases bodd n <;> rfl
    

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mod_two_of_bodd [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_» («term_%_» `n "%" (num "2")) "=" (Term.app `cond [(Term.app `bodd [`n]) (num "1") (num "0")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl [] [] ":=" (Term.app `congr_arg [`bodd (Term.app `mod_add_div [`n (num "2")])]))))
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `not)] "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.show
                "show"
                (Term.forall "∀" [`b] [] "," («term_=_» («term_&&_» `ff "&&" `b) "=" `ff))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.intros "intros" [])
                     "<;>"
                     (Tactic.«tactic_<;>_»
                      (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
                      "<;>"
                      (Tactic.tacticRfl "rfl")))])))))
              ","
              (Tactic.rwRule
               []
               (Term.show
                "show"
                (Term.forall "∀" [`b] [] "," («term_=_» (Term.app `xor [`b `ff]) "=" `b))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.intros "intros" [])
                     "<;>"
                     (Tactic.«tactic_<;>_»
                      (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
                      "<;>"
                      (Tactic.tacticRfl "rfl")))])))))]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `this)] "]") [])
           []
           (Tactic.«tactic_<;>_»
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] (Term.app `mod_two_eq_zero_or_one [`n]))]
             []
             ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
            "<;>"
            (Tactic.«tactic_<;>_»
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
             "<;>"
             (Tactic.tacticRfl "rfl")))])))
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
            (Term.haveIdDecl [] [] ":=" (Term.app `congr_arg [`bodd (Term.app `mod_add_div [`n (num "2")])]))))
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] `not)] "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.show
               "show"
               (Term.forall "∀" [`b] [] "," («term_=_» («term_&&_» `ff "&&" `b) "=" `ff))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.intros "intros" [])
                    "<;>"
                    (Tactic.«tactic_<;>_»
                     (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
                     "<;>"
                     (Tactic.tacticRfl "rfl")))])))))
             ","
             (Tactic.rwRule
              []
              (Term.show
               "show"
               (Term.forall "∀" [`b] [] "," («term_=_» (Term.app `xor [`b `ff]) "=" `b))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Tactic.intros "intros" [])
                    "<;>"
                    (Tactic.«tactic_<;>_»
                     (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
                     "<;>"
                     (Tactic.tacticRfl "rfl")))])))))]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `this)] "]") [])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] (Term.app `mod_two_eq_zero_or_one [`n]))]
            []
            ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
           "<;>"
           (Tactic.«tactic_<;>_»
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
            "<;>"
            (Tactic.tacticRfl "rfl")))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app `mod_two_eq_zero_or_one [`n]))]
        []
        ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
       "<;>"
       (Tactic.«tactic_<;>_»
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
        "<;>"
        (Tactic.tacticRfl "rfl")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
       "<;>"
       (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] (Term.app `mod_two_eq_zero_or_one [`n]))]
       []
       ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mod_two_eq_zero_or_one [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mod_two_eq_zero_or_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `this)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
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
  mod_two_of_bodd
  ( n : ℕ ) : n % 2 = cond bodd n 1 0
  :=
    by
      have := congr_arg bodd mod_add_div n 2
        simp [ not ] at this
        rw
          [
            show ∀ b , ff && b = ff by intros <;> cases b <;> rfl
              ,
              show ∀ b , xor b ff = b by intros <;> cases b <;> rfl
            ]
          at this
        rw [ ← this ]
        cases' mod_two_eq_zero_or_one n with h h <;> rw [ h ] <;> rfl

@[simp]
theorem div2_zero : div2 0 = 0 :=
  rfl

theorem div2_one : div2 1 = 0 :=
  rfl

theorem div2_two : div2 2 = 1 :=
  rfl

@[simp]
theorem div2_succ (n : ℕ) : div2 (succ n) = cond (bodd n) (succ (div2 n)) (div2 n) := by
  unfold bodd div2 bodd_div2 <;> cases bodd_div2 n <;> cases fst <;> rfl

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | 0 => rfl
  | succ n => by
    simp
    refine' Eq.trans _ (congr_arg succ (bodd_add_div2 n))
    cases bodd n <;> simp [cond, not]
    · rw [Nat.add_comm, Nat.zero_add]
      
    · rw [succ_mul, Nat.add_comm 1, Nat.zero_add]
      

theorem div2_val (n) : div2 n = n / 2 := by
  refine' Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_left_cancel (Eq.trans _ (Nat.mod_add_div n 2).symm))
  rw [mod_two_of_bodd, bodd_add_div2]

def bit (b : Bool) : ℕ → ℕ :=
  cond b bit1 bit0

theorem bit0_val (n : Nat) : bit0 n = 2 * n :=
  calc
    n + n = 0 + n + n := by rw [Nat.zero_add]
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

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.def
      "def"
      (Command.declId `bitCasesOn [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`C] [":" (Term.arrow `Nat "→" (Term.sort "Sort" [`u]))] "}")
        (Term.explicitBinder "(" [`n] [] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":" (Term.forall "∀" [`b `n] [] "," (Term.app `C [(Term.app `bit [`b `n])]))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `C [`n]))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `bit_decomp [`n]))] "]") [])
            "<;>"
            (Tactic.apply "apply" `h))])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `bit_decomp [`n]))] "]") [])
           "<;>"
           (Tactic.apply "apply" `h))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `bit_decomp [`n]))] "]") [])
       "<;>"
       (Tactic.apply "apply" `h))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `h)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `bit_decomp [`n]))] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bit_decomp [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bit_decomp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
def bitCasesOn { C : Nat → Sort u } ( n ) ( h : ∀ b n , C bit b n ) : C n := by rw [ ← bit_decomp n ] <;> apply h

theorem bit_zero : bit false 0 = 0 :=
  rfl

def shiftl' (b : Bool) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => bit b (shiftl' n)

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

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.def
      "def"
      (Command.declId `binaryRec [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`C] [":" (Term.arrow `Nat "→" (Term.sort "Sort" [`u]))] "}")
        (Term.explicitBinder "(" [`z] [":" (Term.app `C [(num "0")])] [] ")")
        (Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.forall "∀" [`b `n] [] "," (Term.arrow (Term.app `C [`n]) "→" (Term.app `C [(Term.app `bit [`b `n])])))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.forall "∀" [`n] [] "," (Term.app `C [`n])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`n]]
           "=>"
           (termDepIfThenElse
            "if"
            (Lean.binderIdent `n0)
            ":"
            («term_=_» `n "=" (num "0"))
            "then"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `n0)] "]") [])
                 "<;>"
                 (Tactic.exact "exact" `z))])))
            "else"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `n' [] [] ":=" (Term.app `div2 [`n]))))
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec ":" («term_<_» `n' "<" `n))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.change "change" («term_<_» (Term.app `div2 [`n]) "<" `n) [])
                       []
                       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `div2_val)] "]") [])
                       []
                       (Tactic.apply
                        "apply"
                        (Term.proj
                         («term_<|_» `div_lt_iff_lt_mul "<|" (Term.app `succ_pos [(num "1")]))
                         "."
                         (fieldIdx "2")))
                       []
                       (Tactic.tacticHave_
                        "have"
                        (Term.haveDecl
                         (Term.haveIdDecl
                          []
                          []
                          ":="
                          (Term.app
                           `Nat.mul_lt_mul_of_pos_left
                           [(Term.app `lt_succ_self [(num "1")])
                            (Term.app `lt_of_le_of_ne [`n.zero_le (Term.app `Ne.symm [`n0])])]))))
                       []
                       (tacticRwa__
                        "rwa"
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.mul_one)] "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])]))))))
                []
                (Tactic.«tactic_<;>_»
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     ["←"]
                     (Term.show
                      "show"
                      («term_=_» (Term.app `bit [(Term.app `bodd [`n]) `n']) "=" `n)
                      (Term.fromTerm "from" (Term.app `bit_decomp [`n]))))]
                   "]")
                  [])
                 "<;>"
                 (Tactic.exact "exact" (Term.app `f [(Term.app `bodd [`n]) `n' (Term.app `binary_rec [`n'])])))])))))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `n0)
       ":"
       («term_=_» `n "=" (num "0"))
       "then"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `n0)] "]") [])
            "<;>"
            (Tactic.exact "exact" `z))])))
       "else"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `n' [] [] ":=" (Term.app `div2 [`n]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" («term_<_» `n' "<" `n))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.change "change" («term_<_» (Term.app `div2 [`n]) "<" `n) [])
                  []
                  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `div2_val)] "]") [])
                  []
                  (Tactic.apply
                   "apply"
                   (Term.proj («term_<|_» `div_lt_iff_lt_mul "<|" (Term.app `succ_pos [(num "1")])) "." (fieldIdx "2")))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     []
                     ":="
                     (Term.app
                      `Nat.mul_lt_mul_of_pos_left
                      [(Term.app `lt_succ_self [(num "1")])
                       (Term.app `lt_of_le_of_ne [`n.zero_le (Term.app `Ne.symm [`n0])])]))))
                  []
                  (tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.mul_one)] "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])]))))))
           []
           (Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                ["←"]
                (Term.show
                 "show"
                 («term_=_» (Term.app `bit [(Term.app `bodd [`n]) `n']) "=" `n)
                 (Term.fromTerm "from" (Term.app `bit_decomp [`n]))))]
              "]")
             [])
            "<;>"
            (Tactic.exact "exact" (Term.app `f [(Term.app `bodd [`n]) `n' (Term.app `binary_rec [`n'])])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `n' [] [] ":=" (Term.app `div2 [`n]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" («term_<_» `n' "<" `n))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.change "change" («term_<_» (Term.app `div2 [`n]) "<" `n) [])
                 []
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `div2_val)] "]") [])
                 []
                 (Tactic.apply
                  "apply"
                  (Term.proj («term_<|_» `div_lt_iff_lt_mul "<|" (Term.app `succ_pos [(num "1")])) "." (fieldIdx "2")))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.app
                     `Nat.mul_lt_mul_of_pos_left
                     [(Term.app `lt_succ_self [(num "1")])
                      (Term.app `lt_of_le_of_ne [`n.zero_le (Term.app `Ne.symm [`n0])])]))))
                 []
                 (tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.mul_one)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`this] []))])]))))))
          []
          (Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               ["←"]
               (Term.show
                "show"
                («term_=_» (Term.app `bit [(Term.app `bodd [`n]) `n']) "=" `n)
                (Term.fromTerm "from" (Term.app `bit_decomp [`n]))))]
             "]")
            [])
           "<;>"
           (Tactic.exact "exact" (Term.app `f [(Term.app `bodd [`n]) `n' (Term.app `binary_rec [`n'])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           ["←"]
           (Term.show
            "show"
            («term_=_» (Term.app `bit [(Term.app `bodd [`n]) `n']) "=" `n)
            (Term.fromTerm "from" (Term.app `bit_decomp [`n]))))]
         "]")
        [])
       "<;>"
       (Tactic.exact "exact" (Term.app `f [(Term.app `bodd [`n]) `n' (Term.app `binary_rec [`n'])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `f [(Term.app `bodd [`n]) `n' (Term.app `binary_rec [`n'])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.app `bodd [`n]) `n' (Term.app `binary_rec [`n'])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `binary_rec [`n'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `binary_rec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `binary_rec [`n']) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `bodd [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bodd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `bodd [`n]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          ["←"]
          (Term.show
           "show"
           («term_=_» (Term.app `bit [(Term.app `bodd [`n]) `n']) "=" `n)
           (Term.fromTerm "from" (Term.app `bit_decomp [`n]))))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_» (Term.app `bit [(Term.app `bodd [`n]) `n']) "=" `n)
       (Term.fromTerm "from" (Term.app `bit_decomp [`n])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bit_decomp [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bit_decomp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.app `bit [(Term.app `bodd [`n]) `n']) "=" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `bit [(Term.app `bodd [`n]) `n'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `bodd [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bodd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `bodd [`n]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
def
  binaryRec
  { C : Nat → Sort u } ( z : C 0 ) ( f : ∀ b n , C n → C bit b n ) : ∀ n , C n
  |
    n
    =>
    if
      n0
      :
      n = 0
      then
      by rw [ n0 ] <;> exact z
      else
      by
        let n' := div2 n
          have
            : n' < n
              :=
              by
                change div2 n < n
                  rw [ div2_val ]
                  apply div_lt_iff_lt_mul <| succ_pos 1 . 2
                  have := Nat.mul_lt_mul_of_pos_left lt_succ_self 1 lt_of_le_of_ne n.zero_le Ne.symm n0
                  rwa [ Nat.mul_one ] at this
          rw [ ← show bit bodd n n' = n from bit_decomp n ] <;> exact f bodd n n' binary_rec n'

def size : ℕ → ℕ :=
  binaryRec 0 fun _ _ => succ

def bits : ℕ → List Bool :=
  binaryRec [] fun b _ IH => b :: IH

def bitwise (f : Bool → Bool → Bool) : ℕ → ℕ → ℕ :=
  binaryRec (fun n => cond (f false true) n 0) fun a m Ia =>
    binaryRec (cond (f true false) (bit a m) 0) fun b n _ => bit (f a b) (Ia n)

def lor : ℕ → ℕ → ℕ :=
  bitwise or

def land : ℕ → ℕ → ℕ :=
  bitwise and

def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun a b => a && not b

def lxor : ℕ → ℕ → ℕ :=
  bitwise xor

@[simp]
theorem binary_rec_zero {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) : binaryRec z f 0 = z := by
  rw [binary_rec]
  rfl

-- bitwise ops
theorem bodd_bit (b n) : bodd (bit b n) = b := by rw [bit_val] <;> simp <;> cases b <;> cases bodd n <;> rfl

theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add] <;> cases b <;> exact by decide

theorem shiftl'_add (b m n) : ∀ k, shiftl' b m (n + k) = shiftl' b (shiftl' b m n) k
  | 0 => rfl
  | k + 1 => congr_arg (bit b) (shiftl'_add k)

theorem shiftl_add : ∀ m n k, shiftl m (n + k) = shiftl (shiftl m n) k :=
  shiftl'_add _

theorem shiftr_add (m n) : ∀ k, shiftr m (n + k) = shiftr (shiftr m n) k
  | 0 => rfl
  | k + 1 => congr_arg div2 (shiftr_add k)

theorem shiftl'_sub (b m) : ∀ {n k}, k ≤ n → shiftl' b m (n - k) = shiftr (shiftl' b m n) k
  | n, 0, h => rfl
  | n + 1, k + 1, h => by
    simp [shiftl']
    rw [Nat.add_comm, shiftr_add]
    simp [shiftr, div2_bit]
    apply shiftl'_sub (Nat.le_of_succ_le_succ h)

theorem shiftl_sub : ∀ (m) {n k}, k ≤ n → shiftl m (n - k) = shiftr (shiftl m n) k :=
  shiftl'_sub _

@[simp]
theorem test_bit_zero (b n) : testBit (bit b n) 0 = b :=
  bodd_bit _ _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `test_bit_succ [])
      (Command.declSig
       [(Term.explicitBinder "(" [`m `b `n] [] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `testBit [(Term.app `bit [`b `n]) (Term.app `succ [`m])])
         "="
         (Term.app `testBit [`n `m]))))
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
                 (Term.app `bodd [(Term.app `shiftr [(Term.app `shiftr [(Term.app `bit [`b `n]) (num "1")]) `m])])
                 "="
                 (Term.app `bodd [(Term.app `shiftr [`n `m])])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `shiftr)] "]"] [])
                   "<;>"
                   (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `div2_bit)] "]") []))]))))))
           []
           (Tactic.«tactic_<;>_»
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `shiftr_add) "," (Tactic.rwRule [] `Nat.add_comm)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
            "<;>"
            (Tactic.exact "exact" `this))])))
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
                (Term.app `bodd [(Term.app `shiftr [(Term.app `shiftr [(Term.app `bit [`b `n]) (num "1")]) `m])])
                "="
                (Term.app `bodd [(Term.app `shiftr [`n `m])])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `shiftr)] "]"] [])
                  "<;>"
                  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `div2_bit)] "]") []))]))))))
          []
          (Tactic.«tactic_<;>_»
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `shiftr_add) "," (Tactic.rwRule [] `Nat.add_comm)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           "<;>"
           (Tactic.exact "exact" `this))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `shiftr_add) "," (Tactic.rwRule [] `Nat.add_comm)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       "<;>"
       (Tactic.exact "exact" `this))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `this)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `shiftr_add) "," (Tactic.rwRule [] `Nat.add_comm)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `shiftr_add
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
  test_bit_succ
  ( m b n ) : testBit bit b n succ m = testBit n m
  :=
    by
      have : bodd shiftr shiftr bit b n 1 m = bodd shiftr n m := by dsimp [ shiftr ] <;> rw [ div2_bit ]
        rw [ ← shiftr_add , Nat.add_comm ] at this <;> exact this

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `binary_rec_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`C] [":" (Term.arrow `Nat "→" (Term.sort "Sort" [`u]))] "}")
        (Term.implicitBinder "{" [`z] [":" (Term.app `C [(num "0")])] "}")
        (Term.implicitBinder
         "{"
         [`f]
         [":"
          (Term.forall "∀" [`b `n] [] "," (Term.arrow (Term.app `C [`n]) "→" (Term.app `C [(Term.app `bit [`b `n])])))]
         "}")
        (Term.explicitBinder "(" [`h] [":" («term_=_» (Term.app `f [`false (num "0") `z]) "=" `z)] [] ")")
        (Term.explicitBinder "(" [`b `n] [] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `binaryRec [`z `f (Term.app `bit [`b `n])])
         "="
         (Term.app `f [`b `n (Term.app `binaryRec [`z `f `n])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `binary_rec)] "]") [])
           []
           (Tactic.withCases
            "with_cases"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Classical.«tacticBy_cases_:_» "by_cases" [] («term_=_» (Term.app `bit [`b `n]) "=" (num "0")))])))
           []
           (Tactic.case
            "case"
            [(Tactic.caseArg (Lean.binderIdent `pos) [(Lean.binderIdent `h')])]
            "=>"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `dif_pos [`h']))] "]"] [])
               []
               (Tactic.generalize
                "generalize"
                [(Tactic.generalizeArg
                  []
                  (Term.app `binary_rec._main._pack._proof_1 [(Term.app `bit [`b `n]) `h'])
                  "="
                  `e)]
                [])
               []
               (Tactic.revert "revert" [`e])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl (Term.haveIdDecl [`bf []] [] ":=" (Term.app `bodd_bit [`b `n]))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl (Term.haveIdDecl [`n0 []] [] ":=" (Term.app `div2_bit [`b `n]))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h')] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`bf `n0] []))])
               []
               (Tactic.simp "simp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`bf `n0] []))])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `bf) "," (Tactic.rwRule ["←"] `n0) "," (Tactic.rwRule [] `binary_rec_zero)]
                 "]")
                [])
               []
               (Tactic.intros "intros" [])
               []
               (Tactic.exact "exact" `h.symm)])))
           []
           (Tactic.case
            "case"
            [(Tactic.caseArg (Lean.binderIdent `neg) [(Lean.binderIdent `h')])]
            "=>"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `dif_neg [`h']))] "]"] [])
               []
               (Tactic.generalize
                "generalize"
                [(Tactic.generalizeArg [] (Term.app `binary_rec._main._pack._proof_2 [(Term.app `bit [`b `n])]) "=" `e)]
                [])
               []
               (Tactic.revert "revert" [`e])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `bodd_bit) "," (Tactic.rwRule [] `div2_bit)] "]")
                [])
               []
               (Tactic.intros "intros" [])
               []
               (Tactic.tacticRfl "rfl")])))])))
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
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `binary_rec)] "]") [])
          []
          (Tactic.withCases
           "with_cases"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Classical.«tacticBy_cases_:_» "by_cases" [] («term_=_» (Term.app `bit [`b `n]) "=" (num "0")))])))
          []
          (Tactic.case
           "case"
           [(Tactic.caseArg (Lean.binderIdent `pos) [(Lean.binderIdent `h')])]
           "=>"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `dif_pos [`h']))] "]"] [])
              []
              (Tactic.generalize
               "generalize"
               [(Tactic.generalizeArg
                 []
                 (Term.app `binary_rec._main._pack._proof_1 [(Term.app `bit [`b `n]) `h'])
                 "="
                 `e)]
               [])
              []
              (Tactic.revert "revert" [`e])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl (Term.haveIdDecl [`bf []] [] ":=" (Term.app `bodd_bit [`b `n]))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl (Term.haveIdDecl [`n0 []] [] ":=" (Term.app `div2_bit [`b `n]))))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h')] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`bf `n0] []))])
              []
              (Tactic.simp "simp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`bf `n0] []))])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `bf) "," (Tactic.rwRule ["←"] `n0) "," (Tactic.rwRule [] `binary_rec_zero)]
                "]")
               [])
              []
              (Tactic.intros "intros" [])
              []
              (Tactic.exact "exact" `h.symm)])))
          []
          (Tactic.case
           "case"
           [(Tactic.caseArg (Lean.binderIdent `neg) [(Lean.binderIdent `h')])]
           "=>"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `dif_neg [`h']))] "]"] [])
              []
              (Tactic.generalize
               "generalize"
               [(Tactic.generalizeArg [] (Term.app `binary_rec._main._pack._proof_2 [(Term.app `bit [`b `n])]) "=" `e)]
               [])
              []
              (Tactic.revert "revert" [`e])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `bodd_bit) "," (Tactic.rwRule [] `div2_bit)] "]")
               [])
              []
              (Tactic.intros "intros" [])
              []
              (Tactic.tacticRfl "rfl")])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.case
       "case"
       [(Tactic.caseArg (Lean.binderIdent `neg) [(Lean.binderIdent `h')])]
       "=>"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `dif_neg [`h']))] "]"] [])
          []
          (Tactic.generalize
           "generalize"
           [(Tactic.generalizeArg [] (Term.app `binary_rec._main._pack._proof_2 [(Term.app `bit [`b `n])]) "=" `e)]
           [])
          []
          (Tactic.revert "revert" [`e])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `bodd_bit) "," (Tactic.rwRule [] `div2_bit)] "]")
           [])
          []
          (Tactic.intros "intros" [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `bodd_bit) "," (Tactic.rwRule [] `div2_bit)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `div2_bit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bodd_bit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.revert "revert" [`e])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.generalize
       "generalize"
       [(Tactic.generalizeArg [] (Term.app `binary_rec._main._pack._proof_2 [(Term.app `bit [`b `n])]) "=" `e)]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `binary_rec._main._pack._proof_2 [(Term.app `bit [`b `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bit [`b `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `bit [`b `n]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `binary_rec._main._pack._proof_2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `dif_neg [`h']))] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dif_neg [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dif_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.case
       "case"
       [(Tactic.caseArg (Lean.binderIdent `pos) [(Lean.binderIdent `h')])]
       "=>"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `dif_pos [`h']))] "]"] [])
          []
          (Tactic.generalize
           "generalize"
           [(Tactic.generalizeArg [] (Term.app `binary_rec._main._pack._proof_1 [(Term.app `bit [`b `n]) `h']) "=" `e)]
           [])
          []
          (Tactic.revert "revert" [`e])
          []
          (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`bf []] [] ":=" (Term.app `bodd_bit [`b `n]))))
          []
          (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`n0 []] [] ":=" (Term.app `div2_bit [`b `n]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h')] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`bf `n0] []))])
          []
          (Tactic.simp "simp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`bf `n0] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] `bf) "," (Tactic.rwRule ["←"] `n0) "," (Tactic.rwRule [] `binary_rec_zero)]
            "]")
           [])
          []
          (Tactic.intros "intros" [])
          []
          (Tactic.exact "exact" `h.symm)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h.symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] `bf) "," (Tactic.rwRule ["←"] `n0) "," (Tactic.rwRule [] `binary_rec_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `binary_rec_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n0
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
  binary_rec_eq
  { C : Nat → Sort u } { z : C 0 } { f : ∀ b n , C n → C bit b n } ( h : f false 0 z = z ) ( b n )
    : binaryRec z f bit b n = f b n binaryRec z f n
  :=
    by
      rw [ binary_rec ]
        with_cases by_cases bit b n = 0
        case
          pos h'
          =>
          simp [ dif_pos h' ]
            generalize binary_rec._main._pack._proof_1 bit b n h' = e
            revert e
            have bf := bodd_bit b n
            have n0 := div2_bit b n
            rw [ h' ] at bf n0
            simp at bf n0
            rw [ ← bf , ← n0 , binary_rec_zero ]
            intros
            exact h.symm
        case
          neg h'
          =>
          simp [ dif_neg h' ]
            generalize binary_rec._main._pack._proof_2 bit b n = e
            revert e
            rw [ bodd_bit , div2_bit ]
            intros
            rfl

theorem bitwise_bit_aux {f : Bool → Bool → Bool} (h : f false false = ff) :
    (@binaryRec (fun _ => ℕ) (cond (f true false) (bit false 0) 0) fun b n _ =>
        bit (f false b) (cond (f false true) n 0)) =
      fun n : ℕ => cond (f false true) n 0 :=
  by
  funext n
  apply bit_cases_on n
  intro b n
  rw [binary_rec_eq]
  · cases b <;> try rw [h] <;> induction' fft : f ff tt with <;> simp [cond] <;> rfl
    
  · rw [h, show cond (f ff tt) 0 0 = 0 by cases f ff tt <;> rfl,
        show cond (f tt ff) (bit ff 0) 0 = 0 by cases f tt ff <;> rfl] <;>
      rfl
    

@[simp]
theorem bitwise_zero_left (f : Bool → Bool → Bool) (n) : bitwise f 0 n = cond (f false true) n 0 := by
  unfold bitwise <;> rw [binary_rec_zero]

@[simp]
theorem bitwise_zero_right (f : Bool → Bool → Bool) (h : f false false = ff) (m) :
    bitwise f m 0 = cond (f true false) m 0 := by
  unfold bitwise <;> apply bit_cases_on m <;> intros <;> rw [binary_rec_eq, binary_rec_zero] <;> exact bitwise_bit_aux h

@[simp]
theorem bitwise_zero (f : Bool → Bool → Bool) : bitwise f 0 0 = 0 := by rw [bitwise_zero_left] <;> cases f ff tt <;> rfl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic tactic.swap -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `bitwise_bit [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f] [":" (Term.arrow `Bool "→" (Term.arrow `Bool "→" `Bool))] "}")
        (Term.explicitBinder "(" [`h] [":" («term_=_» (Term.app `f [`false `false]) "=" `ff)] [] ")")
        (Term.explicitBinder "(" [`a `m `b `n] [] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `bitwise [`f (Term.app `bit [`a `m]) (Term.app `bit [`b `n])])
         "="
         (Term.app `bit [(Term.app `f [`a `b]) (Term.app `bitwise [`f `m `n])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.unfold "unfold" [`bitwise] [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `binary_rec_eq) "," (Tactic.rwRule [] `binary_rec_eq)] "]")
            [])
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Tactic.«tactic_<;>_»
               (Tactic.induction'
                "induction'"
                [(Tactic.casesTarget [`ftf ":"] (Term.app `f [`tt `ff]))]
                []
                ["with" []]
                [])
               "<;>"
               (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `cond)] "]"] []))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  []
                  (Term.show
                   "show"
                   («term_=_» (Term.app `f [`a `ff]) "=" `ff)
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.«tactic_<;>_»
                        (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
                        "<;>"
                        (Tactic.assumption "assumption"))])))))]
                "]")
               [])
              [])
             (group
              (Tactic.apply
               "apply"
               (Term.app
                (Term.explicit "@" `congr_arg)
                [(Term.hole "_") (Term.hole "_") (Term.hole "_") (num "0") (Term.app `bit [`ff])]))
              [])
             (group
              (Mathlib.RunCmd.runTac "run_tac" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `tactic.swap) [])]))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  []
                  (Term.show
                   "show"
                   («term_=_» (Term.app `f [`a `ff]) "=" `a)
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.«tactic_<;>_»
                        (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
                        "<;>"
                        (Tactic.assumption "assumption"))])))))]
                "]")
               [])
              [])
             (group (Tactic.apply "apply" (Term.app `congr_arg [(Term.app `bit [`a])])) [])
             (group
              (Tactic.allGoals
               "all_goals"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.apply "apply" (Term.app `bit_cases_on [`m]))
                  []
                  (Tactic.intro "intro" [`a `m])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `binary_rec_eq) "," (Tactic.rwRule [] `binary_rec_zero)]
                    "]")
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule ["←"] (Term.app `bitwise_bit_aux [`h])) "," (Tactic.rwRule [] `ftf)]
                    "]")
                   [])
                  []
                  (Tactic.tacticRfl "rfl")])))
              [])])
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group (Tactic.exact "exact" (Term.app `bitwise_bit_aux [`h])) [])])])))
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
         [(Tactic.unfold "unfold" [`bitwise] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `binary_rec_eq) "," (Tactic.rwRule [] `binary_rec_eq)] "]")
           [])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.«tactic_<;>_»
              (Tactic.induction'
               "induction'"
               [(Tactic.casesTarget [`ftf ":"] (Term.app `f [`tt `ff]))]
               []
               ["with" []]
               [])
              "<;>"
              (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `cond)] "]"] []))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.show
                  "show"
                  («term_=_» (Term.app `f [`a `ff]) "=" `ff)
                  (Term.byTactic'
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.«tactic_<;>_»
                       (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
                       "<;>"
                       (Tactic.assumption "assumption"))])))))]
               "]")
              [])
             [])
            (group
             (Tactic.apply
              "apply"
              (Term.app
               (Term.explicit "@" `congr_arg)
               [(Term.hole "_") (Term.hole "_") (Term.hole "_") (num "0") (Term.app `bit [`ff])]))
             [])
            (group
             (Mathlib.RunCmd.runTac "run_tac" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `tactic.swap) [])]))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.show
                  "show"
                  («term_=_» (Term.app `f [`a `ff]) "=" `a)
                  (Term.byTactic'
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.«tactic_<;>_»
                       (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
                       "<;>"
                       (Tactic.assumption "assumption"))])))))]
               "]")
              [])
             [])
            (group (Tactic.apply "apply" (Term.app `congr_arg [(Term.app `bit [`a])])) [])
            (group
             (Tactic.allGoals
              "all_goals"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.apply "apply" (Term.app `bit_cases_on [`m]))
                 []
                 (Tactic.intro "intro" [`a `m])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `binary_rec_eq) "," (Tactic.rwRule [] `binary_rec_zero)] "]")
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule ["←"] (Term.app `bitwise_bit_aux [`h])) "," (Tactic.rwRule [] `ftf)]
                   "]")
                  [])
                 []
                 (Tactic.tacticRfl "rfl")])))
             [])])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group (Tactic.exact "exact" (Term.app `bitwise_bit_aux [`h])) [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group (Tactic.exact "exact" (Term.app `bitwise_bit_aux [`h])) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `bitwise_bit_aux [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bitwise_bit_aux [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bitwise_bit_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Tactic.«tactic_<;>_»
          (Tactic.induction' "induction'" [(Tactic.casesTarget [`ftf ":"] (Term.app `f [`tt `ff]))] [] ["with" []] [])
          "<;>"
          (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `cond)] "]"] []))
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule
             []
             (Term.show
              "show"
              («term_=_» (Term.app `f [`a `ff]) "=" `ff)
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
                   "<;>"
                   (Tactic.assumption "assumption"))])))))]
           "]")
          [])
         [])
        (group
         (Tactic.apply
          "apply"
          (Term.app
           (Term.explicit "@" `congr_arg)
           [(Term.hole "_") (Term.hole "_") (Term.hole "_") (num "0") (Term.app `bit [`ff])]))
         [])
        (group (Mathlib.RunCmd.runTac "run_tac" (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `tactic.swap) [])])) [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule
             []
             (Term.show
              "show"
              («term_=_» (Term.app `f [`a `ff]) "=" `a)
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
                   "<;>"
                   (Tactic.assumption "assumption"))])))))]
           "]")
          [])
         [])
        (group (Tactic.apply "apply" (Term.app `congr_arg [(Term.app `bit [`a])])) [])
        (group
         (Tactic.allGoals
          "all_goals"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.apply "apply" (Term.app `bit_cases_on [`m]))
             []
             (Tactic.intro "intro" [`a `m])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `binary_rec_eq) "," (Tactic.rwRule [] `binary_rec_zero)] "]")
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] (Term.app `bitwise_bit_aux [`h])) "," (Tactic.rwRule [] `ftf)]
               "]")
              [])
             []
             (Tactic.tacticRfl "rfl")])))
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.allGoals
       "all_goals"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply "apply" (Term.app `bit_cases_on [`m]))
          []
          (Tactic.intro "intro" [`a `m])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `binary_rec_eq) "," (Tactic.rwRule [] `binary_rec_zero)] "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] (Term.app `bitwise_bit_aux [`h])) "," (Tactic.rwRule [] `ftf)]
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
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `bitwise_bit_aux [`h])) "," (Tactic.rwRule [] `ftf)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ftf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bitwise_bit_aux [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bitwise_bit_aux
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
@[ simp ]
  theorem
    bitwise_bit
    { f : Bool → Bool → Bool } ( h : f false false = ff ) ( a m b n )
      : bitwise f bit a m bit b n = bit f a b bitwise f m n
    :=
      by
        unfold bitwise
          rw [ binary_rec_eq , binary_rec_eq ]
          ·
            induction' ftf : f tt ff with <;> dsimp [ cond ]
              rw [ show f a ff = ff by cases a <;> assumption ]
              apply @ congr_arg _ _ _ 0 bit ff
              run_tac tactic.swap
              rw [ show f a ff = a by cases a <;> assumption ]
              apply congr_arg bit a
              all_goals
                apply bit_cases_on m
                  intro a m
                  rw [ binary_rec_eq , binary_rec_zero ]
                  rw [ ← bitwise_bit_aux h , ftf ]
                  rfl
          · exact bitwise_bit_aux h

theorem bitwise_swap {f : Bool → Bool → Bool} (h : f false false = ff) :
    bitwise (Function.swap f) = Function.swap (bitwise f) := by
  funext m n
  revert n
  dsimp [Function.swap]
  apply binary_rec _ (fun a m' IH => _) m <;> intro n
  · rw [bitwise_zero_left, bitwise_zero_right]
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
theorem ldiff_bit : ∀ a m b n, ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) :=
  bitwise_bit rfl

@[simp]
theorem lxor_bit : ∀ a m b n, lxor (bit a m) (bit b n) = bit (xor a b) (lxor m n) :=
  bitwise_bit rfl

@[simp]
theorem test_bit_bitwise {f : Bool → Bool → Bool} (h : f false false = ff) (m n k) :
    testBit (bitwise f m n) k = f (testBit m k) (testBit n k) := by
  revert m n <;>
    induction' k with k IH <;>
      intro m n <;> apply bit_cases_on m <;> intro a m' <;> apply bit_cases_on n <;> intro b n' <;> rw [bitwise_bit h]
  · simp [test_bit_zero]
    
  · simp [test_bit_succ, IH]
    

@[simp]
theorem test_bit_lor : ∀ m n k, testBit (lor m n) k = (testBit m k || testBit n k) :=
  test_bit_bitwise rfl

@[simp]
theorem test_bit_land : ∀ m n k, testBit (land m n) k = (testBit m k && testBit n k) :=
  test_bit_bitwise rfl

@[simp]
theorem test_bit_ldiff : ∀ m n k, testBit (ldiff m n) k = (testBit m k && not (testBit n k)) :=
  test_bit_bitwise rfl

@[simp]
theorem test_bit_lxor : ∀ m n k, testBit (lxor m n) k = xor (testBit m k) (testBit n k) :=
  test_bit_bitwise rfl

end Nat

