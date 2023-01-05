/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.sigma.lex
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Sigma.Basic
import Leanbin.Init.Meta.Default

universe u v

namespace PSigma

section

variable {α : Sort u} {β : α → Sort v}

variable (r : α → α → Prop)

variable (s : ∀ a, β a → β a → Prop)

#print PSigma.Lex /-
-- Lexicographical order based on r and s
inductive Lex : PSigma β → PSigma β → Prop
  | left : ∀ {a₁ : α} (b₁ : β a₁) {a₂ : α} (b₂ : β a₂), r a₁ a₂ → lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  | right : ∀ (a : α) {b₁ b₂ : β a}, s a b₁ b₂ → lex ⟨a, b₁⟩ ⟨a, b₂⟩
#align psigma.lex PSigma.Lex
-/

end

section

open WellFounded Tactic

parameter {α : Sort u}{β : α → Sort v}

parameter {r : α → α → Prop}{s : ∀ a : α, β a → β a → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => Lex r s

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lex_accessible [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [] "}")
        (Term.explicitBinder "(" [`aca] [":" (Term.app `Acc [`r `a])] [] ")")
        (Term.explicitBinder
         "("
         [`acb]
         [":" (Term.forall "∀" [`a] [] "," (Term.app `WellFounded [(Term.app `s [`a])]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`b]
         [(Term.typeSpec ":" (Term.app `β [`a]))]
         ","
         (Term.app `Acc [(Term.app `Lex [`r `s]) (Term.anonymousCtor "⟨" [`a "," `b] "⟩")]))))
      (Command.declValSimple
       ":="
       (Term.app
        `Acc.recOn
        [`aca
         (Term.fun
          "fun"
          (Term.basicFun
           [`xa
            `aca
            (Term.typeAscription
             "("
             (Term.app `iha [])
             ":"
             [(Term.forall
               "∀"
               [`y]
               []
               ","
               (Term.arrow
                (Term.app `r [`y `xa])
                "→"
                (Term.forall
                 "∀"
                 [`b]
                 [(Term.typeSpec ":" (Term.app `β [`y]))]
                 ","
                 (Term.app
                  `Acc
                  [(Term.app `Lex [`r `s]) (Term.anonymousCtor "⟨" [`y "," `b] "⟩")]))))]
             ")")]
           []
           "=>"
           (Term.fun
            "fun"
            (Term.basicFun
             [`b]
             [(Term.typeSpec ":" (Term.app `β [`xa]))]
             "=>"
             (Term.app
              `Acc.recOn
              [(Term.app `WellFounded.apply [(Term.app `acb [`xa]) `b])
               (Term.fun
                "fun"
                (Term.basicFun
                 [`xb
                  `acb
                  (Term.typeAscription
                   "("
                   (Term.app `ihb [])
                   ":"
                   [(Term.forall
                     "∀"
                     [`y]
                     [(Term.typeSpec ":" (Term.app `β [`xa]))]
                     ","
                     (Term.arrow
                      (Term.app `s [`xa `y `xb])
                      "→"
                      (Term.app
                       `Acc
                       [(Term.app `Lex [`r `s]) (Term.anonymousCtor "⟨" [`xa "," `y] "⟩")])))]
                   ")")]
                 []
                 "=>"
                 (Term.app
                  `Acc.intro
                  [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`p
                      (Term.typeAscription
                       "("
                       (Term.app `lt [])
                       ":"
                       [(PSigma.Init.Data.Sigma.Lex.«term_≺_»
                         `p
                         "≺"
                         (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
                       ")")]
                     []
                     "=>"
                     (Term.have
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`aux []]
                        [(Term.typeSpec
                          ":"
                          (Term.arrow
                           («term_=_» `xa "=" `xa)
                           "→"
                           (Term.arrow
                            (Term.app `HEq [`xb `xb])
                            "→"
                            (Term.app `Acc [(Term.app `Lex [`r `s]) `p]))))]
                        ":="
                        (Term.app
                         (Term.explicit "@" `PSigma.Lex.rec_on)
                         [`α
                          `β
                          `r
                          `s
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`p₁ `p₂]
                            []
                            "=>"
                            (Term.arrow
                             («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
                             "→"
                             (Term.arrow
                              (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
                              "→"
                              (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
                          `p
                          (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                          `lt
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
                             (Term.typeAscription
                              "("
                              (Term.app `b₁ [])
                              ":"
                              [(Term.app `β [`a₁])]
                              ")")
                             (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
                             (Term.typeAscription
                              "("
                              (Term.app `b₂ [])
                              ":"
                              [(Term.app `β [`a₂])]
                              ")")
                             (Term.typeAscription
                              "("
                              (Term.app `h [])
                              ":"
                              [(Term.app `r [`a₁ `a₂])]
                              ")")
                             (Term.typeAscription
                              "("
                              (Term.app `eq₂ [])
                              ":"
                              [(«term_=_» `a₂ "=" `xa)]
                              ")")
                             (Term.typeAscription
                              "("
                              (Term.app `eq₃ [])
                              ":"
                              [(Term.app `HEq [`b₂ `xb])]
                              ")")]
                            []
                            "=>"
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.subst "subst" [`eq₂])
                                ";"
                                (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
                             (Term.typeAscription
                              "("
                              (Term.app `b₁ [`b₂])
                              ":"
                              [(Term.app `β [`a])]
                              ")")
                             (Term.typeAscription
                              "("
                              (Term.app `h [])
                              ":"
                              [(Term.app `s [`a `b₁ `b₂])]
                              ")")
                             (Term.typeAscription
                              "("
                              (Term.app `eq₂ [])
                              ":"
                              [(«term_=_» `a "=" `xa)]
                              ")")
                             (Term.typeAscription
                              "("
                              (Term.app `eq₃ [])
                              ":"
                              [(Term.app `HEq [`b₂ `xb])]
                              ")")]
                            []
                            "=>"
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.subst "subst" [`eq₂])
                                []
                                (Tactic.tacticHave_
                                 "have"
                                 (Term.haveDecl
                                  (Term.haveIdDecl
                                   [`new_eq₃ []]
                                   []
                                   ":="
                                   (Term.app `eq_of_heq [`eq₃]))))
                                []
                                (Tactic.subst "subst" [`new_eq₃])
                                []
                                (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))])))
                      []
                      (Term.app `aux [`rfl (Term.app `HEq.refl [`xb])]))))])))])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Acc.recOn
       [`aca
        (Term.fun
         "fun"
         (Term.basicFun
          [`xa
           `aca
           (Term.typeAscription
            "("
            (Term.app `iha [])
            ":"
            [(Term.forall
              "∀"
              [`y]
              []
              ","
              (Term.arrow
               (Term.app `r [`y `xa])
               "→"
               (Term.forall
                "∀"
                [`b]
                [(Term.typeSpec ":" (Term.app `β [`y]))]
                ","
                (Term.app
                 `Acc
                 [(Term.app `Lex [`r `s]) (Term.anonymousCtor "⟨" [`y "," `b] "⟩")]))))]
            ")")]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`b]
            [(Term.typeSpec ":" (Term.app `β [`xa]))]
            "=>"
            (Term.app
             `Acc.recOn
             [(Term.app `WellFounded.apply [(Term.app `acb [`xa]) `b])
              (Term.fun
               "fun"
               (Term.basicFun
                [`xb
                 `acb
                 (Term.typeAscription
                  "("
                  (Term.app `ihb [])
                  ":"
                  [(Term.forall
                    "∀"
                    [`y]
                    [(Term.typeSpec ":" (Term.app `β [`xa]))]
                    ","
                    (Term.arrow
                     (Term.app `s [`xa `y `xb])
                     "→"
                     (Term.app
                      `Acc
                      [(Term.app `Lex [`r `s]) (Term.anonymousCtor "⟨" [`xa "," `y] "⟩")])))]
                  ")")]
                []
                "=>"
                (Term.app
                 `Acc.intro
                 [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`p
                     (Term.typeAscription
                      "("
                      (Term.app `lt [])
                      ":"
                      [(PSigma.Init.Data.Sigma.Lex.«term_≺_»
                        `p
                        "≺"
                        (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
                      ")")]
                    []
                    "=>"
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`aux []]
                       [(Term.typeSpec
                         ":"
                         (Term.arrow
                          («term_=_» `xa "=" `xa)
                          "→"
                          (Term.arrow
                           (Term.app `HEq [`xb `xb])
                           "→"
                           (Term.app `Acc [(Term.app `Lex [`r `s]) `p]))))]
                       ":="
                       (Term.app
                        (Term.explicit "@" `PSigma.Lex.rec_on)
                        [`α
                         `β
                         `r
                         `s
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`p₁ `p₂]
                           []
                           "=>"
                           (Term.arrow
                            («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
                            "→"
                            (Term.arrow
                             (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
                             "→"
                             (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
                         `p
                         (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                         `lt
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
                            (Term.typeAscription
                             "("
                             (Term.app `b₁ [])
                             ":"
                             [(Term.app `β [`a₁])]
                             ")")
                            (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
                            (Term.typeAscription
                             "("
                             (Term.app `b₂ [])
                             ":"
                             [(Term.app `β [`a₂])]
                             ")")
                            (Term.typeAscription
                             "("
                             (Term.app `h [])
                             ":"
                             [(Term.app `r [`a₁ `a₂])]
                             ")")
                            (Term.typeAscription
                             "("
                             (Term.app `eq₂ [])
                             ":"
                             [(«term_=_» `a₂ "=" `xa)]
                             ")")
                            (Term.typeAscription
                             "("
                             (Term.app `eq₃ [])
                             ":"
                             [(Term.app `HEq [`b₂ `xb])]
                             ")")]
                           []
                           "=>"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.subst "subst" [`eq₂])
                               ";"
                               (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
                            (Term.typeAscription
                             "("
                             (Term.app `b₁ [`b₂])
                             ":"
                             [(Term.app `β [`a])]
                             ")")
                            (Term.typeAscription
                             "("
                             (Term.app `h [])
                             ":"
                             [(Term.app `s [`a `b₁ `b₂])]
                             ")")
                            (Term.typeAscription
                             "("
                             (Term.app `eq₂ [])
                             ":"
                             [(«term_=_» `a "=" `xa)]
                             ")")
                            (Term.typeAscription
                             "("
                             (Term.app `eq₃ [])
                             ":"
                             [(Term.app `HEq [`b₂ `xb])]
                             ")")]
                           []
                           "=>"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.subst "subst" [`eq₂])
                               []
                               (Tactic.tacticHave_
                                "have"
                                (Term.haveDecl
                                 (Term.haveIdDecl
                                  [`new_eq₃ []]
                                  []
                                  ":="
                                  (Term.app `eq_of_heq [`eq₃]))))
                               []
                               (Tactic.subst "subst" [`new_eq₃])
                               []
                               (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))])))
                     []
                     (Term.app `aux [`rfl (Term.app `HEq.refl [`xb])]))))])))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`xa
         `aca
         (Term.typeAscription
          "("
          (Term.app `iha [])
          ":"
          [(Term.forall
            "∀"
            [`y]
            []
            ","
            (Term.arrow
             (Term.app `r [`y `xa])
             "→"
             (Term.forall
              "∀"
              [`b]
              [(Term.typeSpec ":" (Term.app `β [`y]))]
              ","
              (Term.app `Acc [(Term.app `Lex [`r `s]) (Term.anonymousCtor "⟨" [`y "," `b] "⟩")]))))]
          ")")]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`b]
          [(Term.typeSpec ":" (Term.app `β [`xa]))]
          "=>"
          (Term.app
           `Acc.recOn
           [(Term.app `WellFounded.apply [(Term.app `acb [`xa]) `b])
            (Term.fun
             "fun"
             (Term.basicFun
              [`xb
               `acb
               (Term.typeAscription
                "("
                (Term.app `ihb [])
                ":"
                [(Term.forall
                  "∀"
                  [`y]
                  [(Term.typeSpec ":" (Term.app `β [`xa]))]
                  ","
                  (Term.arrow
                   (Term.app `s [`xa `y `xb])
                   "→"
                   (Term.app
                    `Acc
                    [(Term.app `Lex [`r `s]) (Term.anonymousCtor "⟨" [`xa "," `y] "⟩")])))]
                ")")]
              []
              "=>"
              (Term.app
               `Acc.intro
               [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`p
                   (Term.typeAscription
                    "("
                    (Term.app `lt [])
                    ":"
                    [(PSigma.Init.Data.Sigma.Lex.«term_≺_»
                      `p
                      "≺"
                      (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
                    ")")]
                  []
                  "=>"
                  (Term.have
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`aux []]
                     [(Term.typeSpec
                       ":"
                       (Term.arrow
                        («term_=_» `xa "=" `xa)
                        "→"
                        (Term.arrow
                         (Term.app `HEq [`xb `xb])
                         "→"
                         (Term.app `Acc [(Term.app `Lex [`r `s]) `p]))))]
                     ":="
                     (Term.app
                      (Term.explicit "@" `PSigma.Lex.rec_on)
                      [`α
                       `β
                       `r
                       `s
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`p₁ `p₂]
                         []
                         "=>"
                         (Term.arrow
                          («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
                          "→"
                          (Term.arrow
                           (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
                           "→"
                           (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
                       `p
                       (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                       `lt
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
                          (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
                          (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
                          (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
                          (Term.typeAscription
                           "("
                           (Term.app `h [])
                           ":"
                           [(Term.app `r [`a₁ `a₂])]
                           ")")
                          (Term.typeAscription
                           "("
                           (Term.app `eq₂ [])
                           ":"
                           [(«term_=_» `a₂ "=" `xa)]
                           ")")
                          (Term.typeAscription
                           "("
                           (Term.app `eq₃ [])
                           ":"
                           [(Term.app `HEq [`b₂ `xb])]
                           ")")]
                         []
                         "=>"
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.subst "subst" [`eq₂])
                             ";"
                             (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
                          (Term.typeAscription
                           "("
                           (Term.app `b₁ [`b₂])
                           ":"
                           [(Term.app `β [`a])]
                           ")")
                          (Term.typeAscription
                           "("
                           (Term.app `h [])
                           ":"
                           [(Term.app `s [`a `b₁ `b₂])]
                           ")")
                          (Term.typeAscription
                           "("
                           (Term.app `eq₂ [])
                           ":"
                           [(«term_=_» `a "=" `xa)]
                           ")")
                          (Term.typeAscription
                           "("
                           (Term.app `eq₃ [])
                           ":"
                           [(Term.app `HEq [`b₂ `xb])]
                           ")")]
                         []
                         "=>"
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.subst "subst" [`eq₂])
                             []
                             (Tactic.tacticHave_
                              "have"
                              (Term.haveDecl
                               (Term.haveIdDecl
                                [`new_eq₃ []]
                                []
                                ":="
                                (Term.app `eq_of_heq [`eq₃]))))
                             []
                             (Tactic.subst "subst" [`new_eq₃])
                             []
                             (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))])))
                   []
                   (Term.app `aux [`rfl (Term.app `HEq.refl [`xb])]))))])))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`b]
        [(Term.typeSpec ":" (Term.app `β [`xa]))]
        "=>"
        (Term.app
         `Acc.recOn
         [(Term.app `WellFounded.apply [(Term.app `acb [`xa]) `b])
          (Term.fun
           "fun"
           (Term.basicFun
            [`xb
             `acb
             (Term.typeAscription
              "("
              (Term.app `ihb [])
              ":"
              [(Term.forall
                "∀"
                [`y]
                [(Term.typeSpec ":" (Term.app `β [`xa]))]
                ","
                (Term.arrow
                 (Term.app `s [`xa `y `xb])
                 "→"
                 (Term.app
                  `Acc
                  [(Term.app `Lex [`r `s]) (Term.anonymousCtor "⟨" [`xa "," `y] "⟩")])))]
              ")")]
            []
            "=>"
            (Term.app
             `Acc.intro
             [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
              (Term.fun
               "fun"
               (Term.basicFun
                [`p
                 (Term.typeAscription
                  "("
                  (Term.app `lt [])
                  ":"
                  [(PSigma.Init.Data.Sigma.Lex.«term_≺_»
                    `p
                    "≺"
                    (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
                  ")")]
                []
                "=>"
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`aux []]
                   [(Term.typeSpec
                     ":"
                     (Term.arrow
                      («term_=_» `xa "=" `xa)
                      "→"
                      (Term.arrow
                       (Term.app `HEq [`xb `xb])
                       "→"
                       (Term.app `Acc [(Term.app `Lex [`r `s]) `p]))))]
                   ":="
                   (Term.app
                    (Term.explicit "@" `PSigma.Lex.rec_on)
                    [`α
                     `β
                     `r
                     `s
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`p₁ `p₂]
                       []
                       "=>"
                       (Term.arrow
                        («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
                        "→"
                        (Term.arrow
                         (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
                         "→"
                         (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
                     `p
                     (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                     `lt
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
                        (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
                        (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
                        (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
                        (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
                        (Term.typeAscription
                         "("
                         (Term.app `eq₂ [])
                         ":"
                         [(«term_=_» `a₂ "=" `xa)]
                         ")")
                        (Term.typeAscription
                         "("
                         (Term.app `eq₃ [])
                         ":"
                         [(Term.app `HEq [`b₂ `xb])]
                         ")")]
                       []
                       "=>"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.subst "subst" [`eq₂])
                           ";"
                           (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
                        (Term.typeAscription "(" (Term.app `b₁ [`b₂]) ":" [(Term.app `β [`a])] ")")
                        (Term.typeAscription
                         "("
                         (Term.app `h [])
                         ":"
                         [(Term.app `s [`a `b₁ `b₂])]
                         ")")
                        (Term.typeAscription
                         "("
                         (Term.app `eq₂ [])
                         ":"
                         [(«term_=_» `a "=" `xa)]
                         ")")
                        (Term.typeAscription
                         "("
                         (Term.app `eq₃ [])
                         ":"
                         [(Term.app `HEq [`b₂ `xb])]
                         ")")]
                       []
                       "=>"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.subst "subst" [`eq₂])
                           []
                           (Tactic.tacticHave_
                            "have"
                            (Term.haveDecl
                             (Term.haveIdDecl [`new_eq₃ []] [] ":=" (Term.app `eq_of_heq [`eq₃]))))
                           []
                           (Tactic.subst "subst" [`new_eq₃])
                           []
                           (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))])))
                 []
                 (Term.app `aux [`rfl (Term.app `HEq.refl [`xb])]))))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Acc.recOn
       [(Term.app `WellFounded.apply [(Term.app `acb [`xa]) `b])
        (Term.fun
         "fun"
         (Term.basicFun
          [`xb
           `acb
           (Term.typeAscription
            "("
            (Term.app `ihb [])
            ":"
            [(Term.forall
              "∀"
              [`y]
              [(Term.typeSpec ":" (Term.app `β [`xa]))]
              ","
              (Term.arrow
               (Term.app `s [`xa `y `xb])
               "→"
               (Term.app
                `Acc
                [(Term.app `Lex [`r `s]) (Term.anonymousCtor "⟨" [`xa "," `y] "⟩")])))]
            ")")]
          []
          "=>"
          (Term.app
           `Acc.intro
           [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
            (Term.fun
             "fun"
             (Term.basicFun
              [`p
               (Term.typeAscription
                "("
                (Term.app `lt [])
                ":"
                [(PSigma.Init.Data.Sigma.Lex.«term_≺_»
                  `p
                  "≺"
                  (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
                ")")]
              []
              "=>"
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`aux []]
                 [(Term.typeSpec
                   ":"
                   (Term.arrow
                    («term_=_» `xa "=" `xa)
                    "→"
                    (Term.arrow
                     (Term.app `HEq [`xb `xb])
                     "→"
                     (Term.app `Acc [(Term.app `Lex [`r `s]) `p]))))]
                 ":="
                 (Term.app
                  (Term.explicit "@" `PSigma.Lex.rec_on)
                  [`α
                   `β
                   `r
                   `s
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`p₁ `p₂]
                     []
                     "=>"
                     (Term.arrow
                      («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
                      "→"
                      (Term.arrow
                       (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
                       "→"
                       (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
                   `p
                   (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                   `lt
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
                      (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
                      (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
                      (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
                      (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
                      (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                      (Term.typeAscription
                       "("
                       (Term.app `eq₃ [])
                       ":"
                       [(Term.app `HEq [`b₂ `xb])]
                       ")")]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.subst "subst" [`eq₂])
                         ";"
                         (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
                      (Term.typeAscription "(" (Term.app `b₁ [`b₂]) ":" [(Term.app `β [`a])] ")")
                      (Term.typeAscription
                       "("
                       (Term.app `h [])
                       ":"
                       [(Term.app `s [`a `b₁ `b₂])]
                       ")")
                      (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a "=" `xa)] ")")
                      (Term.typeAscription
                       "("
                       (Term.app `eq₃ [])
                       ":"
                       [(Term.app `HEq [`b₂ `xb])]
                       ")")]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.subst "subst" [`eq₂])
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl [`new_eq₃ []] [] ":=" (Term.app `eq_of_heq [`eq₃]))))
                         []
                         (Tactic.subst "subst" [`new_eq₃])
                         []
                         (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))])))
               []
               (Term.app `aux [`rfl (Term.app `HEq.refl [`xb])]))))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`xb
         `acb
         (Term.typeAscription
          "("
          (Term.app `ihb [])
          ":"
          [(Term.forall
            "∀"
            [`y]
            [(Term.typeSpec ":" (Term.app `β [`xa]))]
            ","
            (Term.arrow
             (Term.app `s [`xa `y `xb])
             "→"
             (Term.app `Acc [(Term.app `Lex [`r `s]) (Term.anonymousCtor "⟨" [`xa "," `y] "⟩")])))]
          ")")]
        []
        "=>"
        (Term.app
         `Acc.intro
         [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
          (Term.fun
           "fun"
           (Term.basicFun
            [`p
             (Term.typeAscription
              "("
              (Term.app `lt [])
              ":"
              [(PSigma.Init.Data.Sigma.Lex.«term_≺_»
                `p
                "≺"
                (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
              ")")]
            []
            "=>"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`aux []]
               [(Term.typeSpec
                 ":"
                 (Term.arrow
                  («term_=_» `xa "=" `xa)
                  "→"
                  (Term.arrow
                   (Term.app `HEq [`xb `xb])
                   "→"
                   (Term.app `Acc [(Term.app `Lex [`r `s]) `p]))))]
               ":="
               (Term.app
                (Term.explicit "@" `PSigma.Lex.rec_on)
                [`α
                 `β
                 `r
                 `s
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`p₁ `p₂]
                   []
                   "=>"
                   (Term.arrow
                    («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
                    "→"
                    (Term.arrow
                     (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
                     "→"
                     (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
                 `p
                 (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                 `lt
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
                    (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
                    (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
                    (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
                    (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
                    (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                    (Term.typeAscription
                     "("
                     (Term.app `eq₃ [])
                     ":"
                     [(Term.app `HEq [`b₂ `xb])]
                     ")")]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.subst "subst" [`eq₂])
                       ";"
                       (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
                    (Term.typeAscription "(" (Term.app `b₁ [`b₂]) ":" [(Term.app `β [`a])] ")")
                    (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`a `b₁ `b₂])] ")")
                    (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a "=" `xa)] ")")
                    (Term.typeAscription
                     "("
                     (Term.app `eq₃ [])
                     ":"
                     [(Term.app `HEq [`b₂ `xb])]
                     ")")]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.subst "subst" [`eq₂])
                       []
                       (Tactic.tacticHave_
                        "have"
                        (Term.haveDecl
                         (Term.haveIdDecl [`new_eq₃ []] [] ":=" (Term.app `eq_of_heq [`eq₃]))))
                       []
                       (Tactic.subst "subst" [`new_eq₃])
                       []
                       (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))])))
             []
             (Term.app `aux [`rfl (Term.app `HEq.refl [`xb])]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Acc.intro
       [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
        (Term.fun
         "fun"
         (Term.basicFun
          [`p
           (Term.typeAscription
            "("
            (Term.app `lt [])
            ":"
            [(PSigma.Init.Data.Sigma.Lex.«term_≺_»
              `p
              "≺"
              (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
            ")")]
          []
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`aux []]
             [(Term.typeSpec
               ":"
               (Term.arrow
                («term_=_» `xa "=" `xa)
                "→"
                (Term.arrow
                 (Term.app `HEq [`xb `xb])
                 "→"
                 (Term.app `Acc [(Term.app `Lex [`r `s]) `p]))))]
             ":="
             (Term.app
              (Term.explicit "@" `PSigma.Lex.rec_on)
              [`α
               `β
               `r
               `s
               (Term.fun
                "fun"
                (Term.basicFun
                 [`p₁ `p₂]
                 []
                 "=>"
                 (Term.arrow
                  («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
                  "→"
                  (Term.arrow
                   (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
                   "→"
                   (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
               `p
               (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
               `lt
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
                  (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
                  (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
                  (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
                  (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
                  (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                  (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.subst "subst" [`eq₂])
                     ";"
                     (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
                  (Term.typeAscription "(" (Term.app `b₁ [`b₂]) ":" [(Term.app `β [`a])] ")")
                  (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`a `b₁ `b₂])] ")")
                  (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a "=" `xa)] ")")
                  (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.subst "subst" [`eq₂])
                     []
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl [`new_eq₃ []] [] ":=" (Term.app `eq_of_heq [`eq₃]))))
                     []
                     (Tactic.subst "subst" [`new_eq₃])
                     []
                     (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))])))
           []
           (Term.app `aux [`rfl (Term.app `HEq.refl [`xb])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p
         (Term.typeAscription
          "("
          (Term.app `lt [])
          ":"
          [(PSigma.Init.Data.Sigma.Lex.«term_≺_» `p "≺" (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
          ")")]
        []
        "=>"
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`aux []]
           [(Term.typeSpec
             ":"
             (Term.arrow
              («term_=_» `xa "=" `xa)
              "→"
              (Term.arrow
               (Term.app `HEq [`xb `xb])
               "→"
               (Term.app `Acc [(Term.app `Lex [`r `s]) `p]))))]
           ":="
           (Term.app
            (Term.explicit "@" `PSigma.Lex.rec_on)
            [`α
             `β
             `r
             `s
             (Term.fun
              "fun"
              (Term.basicFun
               [`p₁ `p₂]
               []
               "=>"
               (Term.arrow
                («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
                "→"
                (Term.arrow
                 (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
                 "→"
                 (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
             `p
             (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
             `lt
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
                (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
                (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
                (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
                (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
                (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.subst "subst" [`eq₂])
                   ";"
                   (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
                (Term.typeAscription "(" (Term.app `b₁ [`b₂]) ":" [(Term.app `β [`a])] ")")
                (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`a `b₁ `b₂])] ")")
                (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a "=" `xa)] ")")
                (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.subst "subst" [`eq₂])
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl [`new_eq₃ []] [] ":=" (Term.app `eq_of_heq [`eq₃]))))
                   []
                   (Tactic.subst "subst" [`new_eq₃])
                   []
                   (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))])))
         []
         (Term.app `aux [`rfl (Term.app `HEq.refl [`xb])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`aux []]
         [(Term.typeSpec
           ":"
           (Term.arrow
            («term_=_» `xa "=" `xa)
            "→"
            (Term.arrow
             (Term.app `HEq [`xb `xb])
             "→"
             (Term.app `Acc [(Term.app `Lex [`r `s]) `p]))))]
         ":="
         (Term.app
          (Term.explicit "@" `PSigma.Lex.rec_on)
          [`α
           `β
           `r
           `s
           (Term.fun
            "fun"
            (Term.basicFun
             [`p₁ `p₂]
             []
             "=>"
             (Term.arrow
              («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
              "→"
              (Term.arrow
               (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
               "→"
               (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
           `p
           (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
           `lt
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
              (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
              (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
              (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
              (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
              (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
              (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.subst "subst" [`eq₂])
                 ";"
                 (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
              (Term.typeAscription "(" (Term.app `b₁ [`b₂]) ":" [(Term.app `β [`a])] ")")
              (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`a `b₁ `b₂])] ")")
              (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a "=" `xa)] ")")
              (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.subst "subst" [`eq₂])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl [`new_eq₃ []] [] ":=" (Term.app `eq_of_heq [`eq₃]))))
                 []
                 (Tactic.subst "subst" [`new_eq₃])
                 []
                 (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))])))
       []
       (Term.app `aux [`rfl (Term.app `HEq.refl [`xb])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `aux [`rfl (Term.app `HEq.refl [`xb])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HEq.refl [`xb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HEq.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `HEq.refl [`xb]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `PSigma.Lex.rec_on)
       [`α
        `β
        `r
        `s
        (Term.fun
         "fun"
         (Term.basicFun
          [`p₁ `p₂]
          []
          "=>"
          (Term.arrow
           («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
           "→"
           (Term.arrow
            (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
            "→"
            (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
        `p
        (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
        `lt
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
           (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
           (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
           (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
           (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
           (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
           (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.subst "subst" [`eq₂])
              ";"
              (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
           (Term.typeAscription "(" (Term.app `b₁ [`b₂]) ":" [(Term.app `β [`a])] ")")
           (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`a `b₁ `b₂])] ")")
           (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a "=" `xa)] ")")
           (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.subst "subst" [`eq₂])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl (Term.haveIdDecl [`new_eq₃ []] [] ":=" (Term.app `eq_of_heq [`eq₃]))))
              []
              (Tactic.subst "subst" [`new_eq₃])
              []
              (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
         (Term.typeAscription "(" (Term.app `b₁ [`b₂]) ":" [(Term.app `β [`a])] ")")
         (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`a `b₁ `b₂])] ")")
         (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a "=" `xa)] ")")
         (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.subst "subst" [`eq₂])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl (Term.haveIdDecl [`new_eq₃ []] [] ":=" (Term.app `eq_of_heq [`eq₃]))))
            []
            (Tactic.subst "subst" [`new_eq₃])
            []
            (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.subst "subst" [`eq₂])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`new_eq₃ []] [] ":=" (Term.app `eq_of_heq [`eq₃]))))
          []
          (Tactic.subst "subst" [`new_eq₃])
          []
          (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `ihb [`b₁ `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ihb [`b₁ `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ihb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`new_eq₃])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `new_eq₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`new_eq₃ []] [] ":=" (Term.app `eq_of_heq [`eq₃]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_of_heq [`eq₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_of_heq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`eq₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HEq [`b₂ `xb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HEq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq₃ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a "=" `xa)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `a "=" `xa)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq₂ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`a `b₁ `b₂])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `s [`a `b₁ `b₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `b₁ [`b₂]) ":" [(Term.app `β [`a])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `β [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b₁ [`b₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `a []) ":" [`α] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `a [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
         (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
         (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
         (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
         (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
         (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
         (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.subst "subst" [`eq₂])
            ";"
            (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.subst "subst" [`eq₂]) ";" (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `iha [`a₁ `h `b₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `iha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`eq₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HEq [`b₂ `xb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HEq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq₃ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `a₂ "=" `xa)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq₂ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `r [`a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `β [`a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b₂ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `a₂ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `β [`a₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b₁ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `a₁ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.typeAscription "(" (Term.app `a₁ []) ":" [`α] ")")
        (Term.typeAscription "(" (Term.app `b₁ []) ":" [(Term.app `β [`a₁])] ")")
        (Term.typeAscription "(" (Term.app `a₂ []) ":" [`α] ")")
        (Term.typeAscription "(" (Term.app `b₂ []) ":" [(Term.app `β [`a₂])] ")")
        (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
        (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
        (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(Term.app `HEq [`b₂ `xb])] ")")]
       []
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.subst "subst" [`eq₂])
           ";"
           (Tactic.exact "exact" (Term.app `iha [`a₁ `h `b₁]))])))))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `lt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p₁ `p₂]
        []
        "=>"
        (Term.arrow
         («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
         "→"
         (Term.arrow
          (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
          "→"
          (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
       "→"
       (Term.arrow
        (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
        "→"
        (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
       "→"
       (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Acc [(Term.app `Lex [`r `s]) `p₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Lex [`r `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lex
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Lex [`r `s]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Acc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `p₂ "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HEq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj `p₂ "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`p₁ `p₂]
       []
       "=>"
       (Term.arrow
        («term_=_» (Term.proj `p₂ "." (fieldIdx "1")) "=" `xa)
        "→"
        (Term.arrow
         (Term.app `HEq [(Term.proj `p₂ "." (fieldIdx "2")) `xb])
         "→"
         (Term.app `Acc [(Term.paren "(" (Term.app `Lex [`r `s]) ")") `p₁])))))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `PSigma.Lex.rec_on)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PSigma.Lex.rec_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_=_» `xa "=" `xa)
       "→"
       (Term.arrow (Term.app `HEq [`xb `xb]) "→" (Term.app `Acc [(Term.app `Lex [`r `s]) `p])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `HEq [`xb `xb]) "→" (Term.app `Acc [(Term.app `Lex [`r `s]) `p]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Acc [(Term.app `Lex [`r `s]) `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Lex [`r `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lex
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Lex [`r `s]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Acc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `HEq [`xb `xb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HEq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_=_» `xa "=" `xa)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `lt [])
       ":"
       [(PSigma.Init.Data.Sigma.Lex.«term_≺_» `p "≺" (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (PSigma.Init.Data.Sigma.Lex.«term_≺_» `p "≺" (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'PSigma.Init.Data.Sigma.Lex.«term_≺_»', expected 'PSigma.Init.Data.Sigma.Lex.term_≺_._@.Init.Data.Sigma.Lex._hyg.12'
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
theorem
  lex_accessible
  { a } ( aca : Acc r a ) ( acb : ∀ a , WellFounded s a ) : ∀ b : β a , Acc Lex r s ⟨ a , b ⟩
  :=
    Acc.recOn
      aca
        fun
          xa aca ( iha : ∀ y , r y xa → ∀ b : β y , Acc Lex r s ⟨ y , b ⟩ )
            =>
            fun
              b
                : β xa
                =>
                Acc.recOn
                  WellFounded.apply acb xa b
                    fun
                      xb acb ( ihb : ∀ y : β xa , s xa y xb → Acc Lex r s ⟨ xa , y ⟩ )
                        =>
                        Acc.intro
                          ⟨ xa , xb ⟩
                            fun
                              p ( lt : p ≺ ⟨ xa , xb ⟩ )
                                =>
                                have
                                  aux
                                    : xa = xa → HEq xb xb → Acc Lex r s p
                                    :=
                                    @ PSigma.Lex.rec_on
                                      α
                                        β
                                        r
                                        s
                                        fun p₁ p₂ => p₂ . 1 = xa → HEq p₂ . 2 xb → Acc Lex r s p₁
                                        p
                                        ⟨ xa , xb ⟩
                                        lt
                                        fun
                                          ( a₁ : α )
                                              ( b₁ : β a₁ )
                                              ( a₂ : α )
                                              ( b₂ : β a₂ )
                                              ( h : r a₁ a₂ )
                                              ( eq₂ : a₂ = xa )
                                              ( eq₃ : HEq b₂ xb )
                                            =>
                                            by subst eq₂ ; exact iha a₁ h b₁
                                        fun
                                          ( a : α )
                                              ( b₁ b₂ : β a )
                                              ( h : s a b₁ b₂ )
                                              ( eq₂ : a = xa )
                                              ( eq₃ : HEq b₂ xb )
                                            =>
                                            by
                                              subst eq₂
                                                have new_eq₃ := eq_of_heq eq₃
                                                subst new_eq₃
                                                exact ihb b₁ h
                                  aux rfl HEq.refl xb
#align psigma.lex_accessible PSigma.lex_accessible

-- The lexicographical order of well founded relations is well-founded
theorem lex_wf (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lex_accessible (WellFounded.apply ha a) hb b
#align psigma.lex_wf PSigma.lex_wf

end

section

parameter {α : Sort u}{β : Sort v}

def LexNdep (r : α → α → Prop) (s : β → β → Prop) :=
  Lex r fun a : α => s
#align psigma.lex_ndep PSigma.LexNdep

theorem lex_ndep_wf {r : α → α → Prop} {s : β → β → Prop} (ha : WellFounded r)
    (hb : WellFounded s) : WellFounded (lex_ndep r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lex_accessible (WellFounded.apply ha a) (fun x => hb) b
#align psigma.lex_ndep_wf PSigma.lex_ndep_wf

end

section

variable {α : Sort u} {β : Sort v}

variable (r : α → α → Prop)

variable (s : β → β → Prop)

#print PSigma.RevLex /-
-- Reverse lexicographical order based on r and s
inductive RevLex : (@PSigma α fun a => β) → (@PSigma α fun a => β) → Prop
  | left : ∀ {a₁ a₂ : α} (b : β), r a₁ a₂ → rev_lex ⟨a₁, b⟩ ⟨a₂, b⟩
  | right : ∀ (a₁ : α) {b₁ : β} (a₂ : α) {b₂ : β}, s b₁ b₂ → rev_lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
#align psigma.rev_lex PSigma.RevLex
-/

end

section

open WellFounded Tactic

parameter {α : Sort u}{β : Sort v}

parameter {r : α → α → Prop}{s : β → β → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => RevLex r s

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `rev_lex_accessible [])
      (Command.declSig
       [(Term.implicitBinder "{" [`b] [] "}")
        (Term.explicitBinder "(" [`acb] [":" (Term.app `Acc [`s `b])] [] ")")
        (Term.explicitBinder
         "("
         [`aca]
         [":" (Term.forall "∀" [`a] [] "," (Term.app `Acc [`r `a]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`a]
         []
         ","
         (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a "," `b] "⟩")]))))
      (Command.declValSimple
       ":="
       (Term.app
        `Acc.recOn
        [`acb
         (Term.fun
          "fun"
          (Term.basicFun
           [`xb
            `acb
            (Term.typeAscription
             "("
             (Term.app `ihb [])
             ":"
             [(Term.forall
               "∀"
               [`y]
               []
               ","
               (Term.arrow
                (Term.app `s [`y `xb])
                "→"
                (Term.forall
                 "∀"
                 [`a]
                 []
                 ","
                 (Term.app
                  `Acc
                  [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a "," `y] "⟩")]))))]
             ")")]
           []
           "=>"
           (Term.fun
            "fun"
            (Term.basicFun
             [`a]
             []
             "=>"
             (Term.app
              `Acc.recOn
              [(Term.app `aca [`a])
               (Term.fun
                "fun"
                (Term.basicFun
                 [`xa
                  `aca
                  (Term.typeAscription
                   "("
                   (Term.app `iha [])
                   ":"
                   [(Term.forall
                     "∀"
                     [`y]
                     []
                     ","
                     (Term.arrow
                      (Term.app `r [`y `xa])
                      "→"
                      (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`y `xb])])))]
                   ")")]
                 []
                 "=>"
                 (Term.app
                  `Acc.intro
                  [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`p
                      (Term.typeAscription
                       "("
                       (Term.app `lt [])
                       ":"
                       [(PSigma.Init.Data.Sigma.Lex.«term_≺__1»
                         `p
                         "≺"
                         (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
                       ")")]
                     []
                     "=>"
                     (Term.have
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`aux []]
                        [(Term.typeSpec
                          ":"
                          (Term.arrow
                           («term_=_» `xa "=" `xa)
                           "→"
                           (Term.arrow
                            («term_=_» `xb "=" `xb)
                            "→"
                            (Term.app `Acc [(Term.app `RevLex [`r `s]) `p]))))]
                        ":="
                        (Term.app
                         (Term.explicit "@" `RevLex.rec_on)
                         [`α
                          `β
                          `r
                          `s
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`p₁ `p₂]
                            []
                            "=>"
                            (Term.arrow
                             («term_=_» (Term.app `fst [`p₂]) "=" `xa)
                             "→"
                             (Term.arrow
                              («term_=_» (Term.app `snd [`p₂]) "=" `xb)
                              "→"
                              (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
                          `p
                          (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                          `lt
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`a₁
                             `a₂
                             `b
                             (Term.typeAscription
                              "("
                              (Term.app `h [])
                              ":"
                              [(Term.app `r [`a₁ `a₂])]
                              ")")
                             (Term.typeAscription
                              "("
                              (Term.app `eq₂ [])
                              ":"
                              [(«term_=_» `a₂ "=" `xa)]
                              ")")
                             (Term.typeAscription
                              "("
                              (Term.app `eq₃ [])
                              ":"
                              [(«term_=_» `b "=" `xb)]
                              ")")]
                            []
                            "=>"
                            (Term.show
                             "show"
                             (Term.app
                              `Acc
                              [(Term.app `RevLex [`r `s])
                               (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
                             (Term.fromTerm
                              "from"
                              (Term.have
                               "have"
                               (Term.haveDecl
                                (Term.haveIdDecl
                                 [`r₁ []]
                                 [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
                                 ":="
                                 (Term.app `Eq.recOn [`eq₂ `h])))
                               []
                               (Term.have
                                "have"
                                (Term.haveDecl
                                 (Term.haveIdDecl
                                  [`aux []]
                                  [(Term.typeSpec
                                    ":"
                                    (Term.app
                                     `Acc
                                     [(Term.app `RevLex [`r `s])
                                      (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
                                  ":="
                                  (Term.app `iha [`a₁ `r₁])))
                                []
                                (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`a₁
                             `b₁
                             `a₂
                             `b₂
                             (Term.typeAscription
                              "("
                              (Term.app `h [])
                              ":"
                              [(Term.app `s [`b₁ `b₂])]
                              ")")
                             (Term.typeAscription
                              "("
                              (Term.app `eq₂ [])
                              ":"
                              [(«term_=_» `a₂ "=" `xa)]
                              ")")
                             (Term.typeAscription
                              "("
                              (Term.app `eq₃ [])
                              ":"
                              [(«term_=_» `b₂ "=" `xb)]
                              ")")]
                            []
                            "=>"
                            (Term.show
                             "show"
                             (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
                             (Term.fromTerm
                              "from"
                              (Term.have
                               "have"
                               (Term.haveDecl
                                (Term.haveIdDecl
                                 [`s₁ []]
                                 [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
                                 ":="
                                 (Term.app `Eq.recOn [`eq₃ `h])))
                               []
                               (Term.app `ihb [`b₁ `s₁ `a₁]))))))])))
                      []
                      (Term.app `aux [`rfl `rfl]))))])))])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Acc.recOn
       [`acb
        (Term.fun
         "fun"
         (Term.basicFun
          [`xb
           `acb
           (Term.typeAscription
            "("
            (Term.app `ihb [])
            ":"
            [(Term.forall
              "∀"
              [`y]
              []
              ","
              (Term.arrow
               (Term.app `s [`y `xb])
               "→"
               (Term.forall
                "∀"
                [`a]
                []
                ","
                (Term.app
                 `Acc
                 [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a "," `y] "⟩")]))))]
            ")")]
          []
          "=>"
          (Term.fun
           "fun"
           (Term.basicFun
            [`a]
            []
            "=>"
            (Term.app
             `Acc.recOn
             [(Term.app `aca [`a])
              (Term.fun
               "fun"
               (Term.basicFun
                [`xa
                 `aca
                 (Term.typeAscription
                  "("
                  (Term.app `iha [])
                  ":"
                  [(Term.forall
                    "∀"
                    [`y]
                    []
                    ","
                    (Term.arrow
                     (Term.app `r [`y `xa])
                     "→"
                     (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`y `xb])])))]
                  ")")]
                []
                "=>"
                (Term.app
                 `Acc.intro
                 [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`p
                     (Term.typeAscription
                      "("
                      (Term.app `lt [])
                      ":"
                      [(PSigma.Init.Data.Sigma.Lex.«term_≺__1»
                        `p
                        "≺"
                        (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
                      ")")]
                    []
                    "=>"
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`aux []]
                       [(Term.typeSpec
                         ":"
                         (Term.arrow
                          («term_=_» `xa "=" `xa)
                          "→"
                          (Term.arrow
                           («term_=_» `xb "=" `xb)
                           "→"
                           (Term.app `Acc [(Term.app `RevLex [`r `s]) `p]))))]
                       ":="
                       (Term.app
                        (Term.explicit "@" `RevLex.rec_on)
                        [`α
                         `β
                         `r
                         `s
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`p₁ `p₂]
                           []
                           "=>"
                           (Term.arrow
                            («term_=_» (Term.app `fst [`p₂]) "=" `xa)
                            "→"
                            (Term.arrow
                             («term_=_» (Term.app `snd [`p₂]) "=" `xb)
                             "→"
                             (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
                         `p
                         (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                         `lt
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`a₁
                            `a₂
                            `b
                            (Term.typeAscription
                             "("
                             (Term.app `h [])
                             ":"
                             [(Term.app `r [`a₁ `a₂])]
                             ")")
                            (Term.typeAscription
                             "("
                             (Term.app `eq₂ [])
                             ":"
                             [(«term_=_» `a₂ "=" `xa)]
                             ")")
                            (Term.typeAscription
                             "("
                             (Term.app `eq₃ [])
                             ":"
                             [(«term_=_» `b "=" `xb)]
                             ")")]
                           []
                           "=>"
                           (Term.show
                            "show"
                            (Term.app
                             `Acc
                             [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
                            (Term.fromTerm
                             "from"
                             (Term.have
                              "have"
                              (Term.haveDecl
                               (Term.haveIdDecl
                                [`r₁ []]
                                [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
                                ":="
                                (Term.app `Eq.recOn [`eq₂ `h])))
                              []
                              (Term.have
                               "have"
                               (Term.haveDecl
                                (Term.haveIdDecl
                                 [`aux []]
                                 [(Term.typeSpec
                                   ":"
                                   (Term.app
                                    `Acc
                                    [(Term.app `RevLex [`r `s])
                                     (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
                                 ":="
                                 (Term.app `iha [`a₁ `r₁])))
                               []
                               (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`a₁
                            `b₁
                            `a₂
                            `b₂
                            (Term.typeAscription
                             "("
                             (Term.app `h [])
                             ":"
                             [(Term.app `s [`b₁ `b₂])]
                             ")")
                            (Term.typeAscription
                             "("
                             (Term.app `eq₂ [])
                             ":"
                             [(«term_=_» `a₂ "=" `xa)]
                             ")")
                            (Term.typeAscription
                             "("
                             (Term.app `eq₃ [])
                             ":"
                             [(«term_=_» `b₂ "=" `xb)]
                             ")")]
                           []
                           "=>"
                           (Term.show
                            "show"
                            (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
                            (Term.fromTerm
                             "from"
                             (Term.have
                              "have"
                              (Term.haveDecl
                               (Term.haveIdDecl
                                [`s₁ []]
                                [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
                                ":="
                                (Term.app `Eq.recOn [`eq₃ `h])))
                              []
                              (Term.app `ihb [`b₁ `s₁ `a₁]))))))])))
                     []
                     (Term.app `aux [`rfl `rfl]))))])))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`xb
         `acb
         (Term.typeAscription
          "("
          (Term.app `ihb [])
          ":"
          [(Term.forall
            "∀"
            [`y]
            []
            ","
            (Term.arrow
             (Term.app `s [`y `xb])
             "→"
             (Term.forall
              "∀"
              [`a]
              []
              ","
              (Term.app
               `Acc
               [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a "," `y] "⟩")]))))]
          ")")]
        []
        "=>"
        (Term.fun
         "fun"
         (Term.basicFun
          [`a]
          []
          "=>"
          (Term.app
           `Acc.recOn
           [(Term.app `aca [`a])
            (Term.fun
             "fun"
             (Term.basicFun
              [`xa
               `aca
               (Term.typeAscription
                "("
                (Term.app `iha [])
                ":"
                [(Term.forall
                  "∀"
                  [`y]
                  []
                  ","
                  (Term.arrow
                   (Term.app `r [`y `xa])
                   "→"
                   (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`y `xb])])))]
                ")")]
              []
              "=>"
              (Term.app
               `Acc.intro
               [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`p
                   (Term.typeAscription
                    "("
                    (Term.app `lt [])
                    ":"
                    [(PSigma.Init.Data.Sigma.Lex.«term_≺__1»
                      `p
                      "≺"
                      (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
                    ")")]
                  []
                  "=>"
                  (Term.have
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`aux []]
                     [(Term.typeSpec
                       ":"
                       (Term.arrow
                        («term_=_» `xa "=" `xa)
                        "→"
                        (Term.arrow
                         («term_=_» `xb "=" `xb)
                         "→"
                         (Term.app `Acc [(Term.app `RevLex [`r `s]) `p]))))]
                     ":="
                     (Term.app
                      (Term.explicit "@" `RevLex.rec_on)
                      [`α
                       `β
                       `r
                       `s
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`p₁ `p₂]
                         []
                         "=>"
                         (Term.arrow
                          («term_=_» (Term.app `fst [`p₂]) "=" `xa)
                          "→"
                          (Term.arrow
                           («term_=_» (Term.app `snd [`p₂]) "=" `xb)
                           "→"
                           (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
                       `p
                       (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                       `lt
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`a₁
                          `a₂
                          `b
                          (Term.typeAscription
                           "("
                           (Term.app `h [])
                           ":"
                           [(Term.app `r [`a₁ `a₂])]
                           ")")
                          (Term.typeAscription
                           "("
                           (Term.app `eq₂ [])
                           ":"
                           [(«term_=_» `a₂ "=" `xa)]
                           ")")
                          (Term.typeAscription
                           "("
                           (Term.app `eq₃ [])
                           ":"
                           [(«term_=_» `b "=" `xb)]
                           ")")]
                         []
                         "=>"
                         (Term.show
                          "show"
                          (Term.app
                           `Acc
                           [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
                          (Term.fromTerm
                           "from"
                           (Term.have
                            "have"
                            (Term.haveDecl
                             (Term.haveIdDecl
                              [`r₁ []]
                              [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
                              ":="
                              (Term.app `Eq.recOn [`eq₂ `h])))
                            []
                            (Term.have
                             "have"
                             (Term.haveDecl
                              (Term.haveIdDecl
                               [`aux []]
                               [(Term.typeSpec
                                 ":"
                                 (Term.app
                                  `Acc
                                  [(Term.app `RevLex [`r `s])
                                   (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
                               ":="
                               (Term.app `iha [`a₁ `r₁])))
                             []
                             (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [`a₁
                          `b₁
                          `a₂
                          `b₂
                          (Term.typeAscription
                           "("
                           (Term.app `h [])
                           ":"
                           [(Term.app `s [`b₁ `b₂])]
                           ")")
                          (Term.typeAscription
                           "("
                           (Term.app `eq₂ [])
                           ":"
                           [(«term_=_» `a₂ "=" `xa)]
                           ")")
                          (Term.typeAscription
                           "("
                           (Term.app `eq₃ [])
                           ":"
                           [(«term_=_» `b₂ "=" `xb)]
                           ")")]
                         []
                         "=>"
                         (Term.show
                          "show"
                          (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
                          (Term.fromTerm
                           "from"
                           (Term.have
                            "have"
                            (Term.haveDecl
                             (Term.haveIdDecl
                              [`s₁ []]
                              [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
                              ":="
                              (Term.app `Eq.recOn [`eq₃ `h])))
                            []
                            (Term.app `ihb [`b₁ `s₁ `a₁]))))))])))
                   []
                   (Term.app `aux [`rfl `rfl]))))])))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.app
         `Acc.recOn
         [(Term.app `aca [`a])
          (Term.fun
           "fun"
           (Term.basicFun
            [`xa
             `aca
             (Term.typeAscription
              "("
              (Term.app `iha [])
              ":"
              [(Term.forall
                "∀"
                [`y]
                []
                ","
                (Term.arrow
                 (Term.app `r [`y `xa])
                 "→"
                 (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`y `xb])])))]
              ")")]
            []
            "=>"
            (Term.app
             `Acc.intro
             [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
              (Term.fun
               "fun"
               (Term.basicFun
                [`p
                 (Term.typeAscription
                  "("
                  (Term.app `lt [])
                  ":"
                  [(PSigma.Init.Data.Sigma.Lex.«term_≺__1»
                    `p
                    "≺"
                    (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
                  ")")]
                []
                "=>"
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`aux []]
                   [(Term.typeSpec
                     ":"
                     (Term.arrow
                      («term_=_» `xa "=" `xa)
                      "→"
                      (Term.arrow
                       («term_=_» `xb "=" `xb)
                       "→"
                       (Term.app `Acc [(Term.app `RevLex [`r `s]) `p]))))]
                   ":="
                   (Term.app
                    (Term.explicit "@" `RevLex.rec_on)
                    [`α
                     `β
                     `r
                     `s
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`p₁ `p₂]
                       []
                       "=>"
                       (Term.arrow
                        («term_=_» (Term.app `fst [`p₂]) "=" `xa)
                        "→"
                        (Term.arrow
                         («term_=_» (Term.app `snd [`p₂]) "=" `xb)
                         "→"
                         (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
                     `p
                     (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                     `lt
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`a₁
                        `a₂
                        `b
                        (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
                        (Term.typeAscription
                         "("
                         (Term.app `eq₂ [])
                         ":"
                         [(«term_=_» `a₂ "=" `xa)]
                         ")")
                        (Term.typeAscription
                         "("
                         (Term.app `eq₃ [])
                         ":"
                         [(«term_=_» `b "=" `xb)]
                         ")")]
                       []
                       "=>"
                       (Term.show
                        "show"
                        (Term.app
                         `Acc
                         [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
                        (Term.fromTerm
                         "from"
                         (Term.have
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`r₁ []]
                            [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
                            ":="
                            (Term.app `Eq.recOn [`eq₂ `h])))
                          []
                          (Term.have
                           "have"
                           (Term.haveDecl
                            (Term.haveIdDecl
                             [`aux []]
                             [(Term.typeSpec
                               ":"
                               (Term.app
                                `Acc
                                [(Term.app `RevLex [`r `s])
                                 (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
                             ":="
                             (Term.app `iha [`a₁ `r₁])))
                           []
                           (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`a₁
                        `b₁
                        `a₂
                        `b₂
                        (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`b₁ `b₂])] ")")
                        (Term.typeAscription
                         "("
                         (Term.app `eq₂ [])
                         ":"
                         [(«term_=_» `a₂ "=" `xa)]
                         ")")
                        (Term.typeAscription
                         "("
                         (Term.app `eq₃ [])
                         ":"
                         [(«term_=_» `b₂ "=" `xb)]
                         ")")]
                       []
                       "=>"
                       (Term.show
                        "show"
                        (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
                        (Term.fromTerm
                         "from"
                         (Term.have
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`s₁ []]
                            [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
                            ":="
                            (Term.app `Eq.recOn [`eq₃ `h])))
                          []
                          (Term.app `ihb [`b₁ `s₁ `a₁]))))))])))
                 []
                 (Term.app `aux [`rfl `rfl]))))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Acc.recOn
       [(Term.app `aca [`a])
        (Term.fun
         "fun"
         (Term.basicFun
          [`xa
           `aca
           (Term.typeAscription
            "("
            (Term.app `iha [])
            ":"
            [(Term.forall
              "∀"
              [`y]
              []
              ","
              (Term.arrow
               (Term.app `r [`y `xa])
               "→"
               (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`y `xb])])))]
            ")")]
          []
          "=>"
          (Term.app
           `Acc.intro
           [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
            (Term.fun
             "fun"
             (Term.basicFun
              [`p
               (Term.typeAscription
                "("
                (Term.app `lt [])
                ":"
                [(PSigma.Init.Data.Sigma.Lex.«term_≺__1»
                  `p
                  "≺"
                  (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
                ")")]
              []
              "=>"
              (Term.have
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`aux []]
                 [(Term.typeSpec
                   ":"
                   (Term.arrow
                    («term_=_» `xa "=" `xa)
                    "→"
                    (Term.arrow
                     («term_=_» `xb "=" `xb)
                     "→"
                     (Term.app `Acc [(Term.app `RevLex [`r `s]) `p]))))]
                 ":="
                 (Term.app
                  (Term.explicit "@" `RevLex.rec_on)
                  [`α
                   `β
                   `r
                   `s
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`p₁ `p₂]
                     []
                     "=>"
                     (Term.arrow
                      («term_=_» (Term.app `fst [`p₂]) "=" `xa)
                      "→"
                      (Term.arrow
                       («term_=_» (Term.app `snd [`p₂]) "=" `xb)
                       "→"
                       (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
                   `p
                   (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                   `lt
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`a₁
                      `a₂
                      `b
                      (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
                      (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                      (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b "=" `xb)] ")")]
                     []
                     "=>"
                     (Term.show
                      "show"
                      (Term.app
                       `Acc
                       [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
                      (Term.fromTerm
                       "from"
                       (Term.have
                        "have"
                        (Term.haveDecl
                         (Term.haveIdDecl
                          [`r₁ []]
                          [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
                          ":="
                          (Term.app `Eq.recOn [`eq₂ `h])))
                        []
                        (Term.have
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           [`aux []]
                           [(Term.typeSpec
                             ":"
                             (Term.app
                              `Acc
                              [(Term.app `RevLex [`r `s])
                               (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
                           ":="
                           (Term.app `iha [`a₁ `r₁])))
                         []
                         (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`a₁
                      `b₁
                      `a₂
                      `b₂
                      (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`b₁ `b₂])] ")")
                      (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                      (Term.typeAscription
                       "("
                       (Term.app `eq₃ [])
                       ":"
                       [(«term_=_» `b₂ "=" `xb)]
                       ")")]
                     []
                     "=>"
                     (Term.show
                      "show"
                      (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
                      (Term.fromTerm
                       "from"
                       (Term.have
                        "have"
                        (Term.haveDecl
                         (Term.haveIdDecl
                          [`s₁ []]
                          [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
                          ":="
                          (Term.app `Eq.recOn [`eq₃ `h])))
                        []
                        (Term.app `ihb [`b₁ `s₁ `a₁]))))))])))
               []
               (Term.app `aux [`rfl `rfl]))))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`xa
         `aca
         (Term.typeAscription
          "("
          (Term.app `iha [])
          ":"
          [(Term.forall
            "∀"
            [`y]
            []
            ","
            (Term.arrow
             (Term.app `r [`y `xa])
             "→"
             (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`y `xb])])))]
          ")")]
        []
        "=>"
        (Term.app
         `Acc.intro
         [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
          (Term.fun
           "fun"
           (Term.basicFun
            [`p
             (Term.typeAscription
              "("
              (Term.app `lt [])
              ":"
              [(PSigma.Init.Data.Sigma.Lex.«term_≺__1»
                `p
                "≺"
                (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
              ")")]
            []
            "=>"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`aux []]
               [(Term.typeSpec
                 ":"
                 (Term.arrow
                  («term_=_» `xa "=" `xa)
                  "→"
                  (Term.arrow
                   («term_=_» `xb "=" `xb)
                   "→"
                   (Term.app `Acc [(Term.app `RevLex [`r `s]) `p]))))]
               ":="
               (Term.app
                (Term.explicit "@" `RevLex.rec_on)
                [`α
                 `β
                 `r
                 `s
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`p₁ `p₂]
                   []
                   "=>"
                   (Term.arrow
                    («term_=_» (Term.app `fst [`p₂]) "=" `xa)
                    "→"
                    (Term.arrow
                     («term_=_» (Term.app `snd [`p₂]) "=" `xb)
                     "→"
                     (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
                 `p
                 (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
                 `lt
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`a₁
                    `a₂
                    `b
                    (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
                    (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                    (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b "=" `xb)] ")")]
                   []
                   "=>"
                   (Term.show
                    "show"
                    (Term.app
                     `Acc
                     [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
                    (Term.fromTerm
                     "from"
                     (Term.have
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`r₁ []]
                        [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
                        ":="
                        (Term.app `Eq.recOn [`eq₂ `h])))
                      []
                      (Term.have
                       "have"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         [`aux []]
                         [(Term.typeSpec
                           ":"
                           (Term.app
                            `Acc
                            [(Term.app `RevLex [`r `s])
                             (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
                         ":="
                         (Term.app `iha [`a₁ `r₁])))
                       []
                       (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`a₁
                    `b₁
                    `a₂
                    `b₂
                    (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`b₁ `b₂])] ")")
                    (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                    (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b₂ "=" `xb)] ")")]
                   []
                   "=>"
                   (Term.show
                    "show"
                    (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
                    (Term.fromTerm
                     "from"
                     (Term.have
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`s₁ []]
                        [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
                        ":="
                        (Term.app `Eq.recOn [`eq₃ `h])))
                      []
                      (Term.app `ihb [`b₁ `s₁ `a₁]))))))])))
             []
             (Term.app `aux [`rfl `rfl]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Acc.intro
       [(Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
        (Term.fun
         "fun"
         (Term.basicFun
          [`p
           (Term.typeAscription
            "("
            (Term.app `lt [])
            ":"
            [(PSigma.Init.Data.Sigma.Lex.«term_≺__1»
              `p
              "≺"
              (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
            ")")]
          []
          "=>"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`aux []]
             [(Term.typeSpec
               ":"
               (Term.arrow
                («term_=_» `xa "=" `xa)
                "→"
                (Term.arrow
                 («term_=_» `xb "=" `xb)
                 "→"
                 (Term.app `Acc [(Term.app `RevLex [`r `s]) `p]))))]
             ":="
             (Term.app
              (Term.explicit "@" `RevLex.rec_on)
              [`α
               `β
               `r
               `s
               (Term.fun
                "fun"
                (Term.basicFun
                 [`p₁ `p₂]
                 []
                 "=>"
                 (Term.arrow
                  («term_=_» (Term.app `fst [`p₂]) "=" `xa)
                  "→"
                  (Term.arrow
                   («term_=_» (Term.app `snd [`p₂]) "=" `xb)
                   "→"
                   (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
               `p
               (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
               `lt
               (Term.fun
                "fun"
                (Term.basicFun
                 [`a₁
                  `a₂
                  `b
                  (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
                  (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                  (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b "=" `xb)] ")")]
                 []
                 "=>"
                 (Term.show
                  "show"
                  (Term.app
                   `Acc
                   [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
                  (Term.fromTerm
                   "from"
                   (Term.have
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`r₁ []]
                      [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
                      ":="
                      (Term.app `Eq.recOn [`eq₂ `h])))
                    []
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`aux []]
                       [(Term.typeSpec
                         ":"
                         (Term.app
                          `Acc
                          [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
                       ":="
                       (Term.app `iha [`a₁ `r₁])))
                     []
                     (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
               (Term.fun
                "fun"
                (Term.basicFun
                 [`a₁
                  `b₁
                  `a₂
                  `b₂
                  (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`b₁ `b₂])] ")")
                  (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                  (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b₂ "=" `xb)] ")")]
                 []
                 "=>"
                 (Term.show
                  "show"
                  (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
                  (Term.fromTerm
                   "from"
                   (Term.have
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`s₁ []]
                      [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
                      ":="
                      (Term.app `Eq.recOn [`eq₃ `h])))
                    []
                    (Term.app `ihb [`b₁ `s₁ `a₁]))))))])))
           []
           (Term.app `aux [`rfl `rfl]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p
         (Term.typeAscription
          "("
          (Term.app `lt [])
          ":"
          [(PSigma.Init.Data.Sigma.Lex.«term_≺__1»
            `p
            "≺"
            (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
          ")")]
        []
        "=>"
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`aux []]
           [(Term.typeSpec
             ":"
             (Term.arrow
              («term_=_» `xa "=" `xa)
              "→"
              (Term.arrow
               («term_=_» `xb "=" `xb)
               "→"
               (Term.app `Acc [(Term.app `RevLex [`r `s]) `p]))))]
           ":="
           (Term.app
            (Term.explicit "@" `RevLex.rec_on)
            [`α
             `β
             `r
             `s
             (Term.fun
              "fun"
              (Term.basicFun
               [`p₁ `p₂]
               []
               "=>"
               (Term.arrow
                («term_=_» (Term.app `fst [`p₂]) "=" `xa)
                "→"
                (Term.arrow
                 («term_=_» (Term.app `snd [`p₂]) "=" `xb)
                 "→"
                 (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
             `p
             (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
             `lt
             (Term.fun
              "fun"
              (Term.basicFun
               [`a₁
                `a₂
                `b
                (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
                (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b "=" `xb)] ")")]
               []
               "=>"
               (Term.show
                "show"
                (Term.app
                 `Acc
                 [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
                (Term.fromTerm
                 "from"
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`r₁ []]
                    [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
                    ":="
                    (Term.app `Eq.recOn [`eq₂ `h])))
                  []
                  (Term.have
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`aux []]
                     [(Term.typeSpec
                       ":"
                       (Term.app
                        `Acc
                        [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
                     ":="
                     (Term.app `iha [`a₁ `r₁])))
                   []
                   (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
             (Term.fun
              "fun"
              (Term.basicFun
               [`a₁
                `b₁
                `a₂
                `b₂
                (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`b₁ `b₂])] ")")
                (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
                (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b₂ "=" `xb)] ")")]
               []
               "=>"
               (Term.show
                "show"
                (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
                (Term.fromTerm
                 "from"
                 (Term.have
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`s₁ []]
                    [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
                    ":="
                    (Term.app `Eq.recOn [`eq₃ `h])))
                  []
                  (Term.app `ihb [`b₁ `s₁ `a₁]))))))])))
         []
         (Term.app `aux [`rfl `rfl]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`aux []]
         [(Term.typeSpec
           ":"
           (Term.arrow
            («term_=_» `xa "=" `xa)
            "→"
            (Term.arrow
             («term_=_» `xb "=" `xb)
             "→"
             (Term.app `Acc [(Term.app `RevLex [`r `s]) `p]))))]
         ":="
         (Term.app
          (Term.explicit "@" `RevLex.rec_on)
          [`α
           `β
           `r
           `s
           (Term.fun
            "fun"
            (Term.basicFun
             [`p₁ `p₂]
             []
             "=>"
             (Term.arrow
              («term_=_» (Term.app `fst [`p₂]) "=" `xa)
              "→"
              (Term.arrow
               («term_=_» (Term.app `snd [`p₂]) "=" `xb)
               "→"
               (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
           `p
           (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
           `lt
           (Term.fun
            "fun"
            (Term.basicFun
             [`a₁
              `a₂
              `b
              (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
              (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
              (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b "=" `xb)] ")")]
             []
             "=>"
             (Term.show
              "show"
              (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
              (Term.fromTerm
               "from"
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`r₁ []]
                  [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
                  ":="
                  (Term.app `Eq.recOn [`eq₂ `h])))
                []
                (Term.have
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`aux []]
                   [(Term.typeSpec
                     ":"
                     (Term.app
                      `Acc
                      [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
                   ":="
                   (Term.app `iha [`a₁ `r₁])))
                 []
                 (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
           (Term.fun
            "fun"
            (Term.basicFun
             [`a₁
              `b₁
              `a₂
              `b₂
              (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`b₁ `b₂])] ")")
              (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
              (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b₂ "=" `xb)] ")")]
             []
             "=>"
             (Term.show
              "show"
              (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
              (Term.fromTerm
               "from"
               (Term.have
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`s₁ []]
                  [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
                  ":="
                  (Term.app `Eq.recOn [`eq₃ `h])))
                []
                (Term.app `ihb [`b₁ `s₁ `a₁]))))))])))
       []
       (Term.app `aux [`rfl `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `aux [`rfl `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `RevLex.rec_on)
       [`α
        `β
        `r
        `s
        (Term.fun
         "fun"
         (Term.basicFun
          [`p₁ `p₂]
          []
          "=>"
          (Term.arrow
           («term_=_» (Term.app `fst [`p₂]) "=" `xa)
           "→"
           (Term.arrow
            («term_=_» (Term.app `snd [`p₂]) "=" `xb)
            "→"
            (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
        `p
        (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
        `lt
        (Term.fun
         "fun"
         (Term.basicFun
          [`a₁
           `a₂
           `b
           (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
           (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
           (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b "=" `xb)] ")")]
          []
          "=>"
          (Term.show
           "show"
           (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
           (Term.fromTerm
            "from"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`r₁ []]
               [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
               ":="
               (Term.app `Eq.recOn [`eq₂ `h])))
             []
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`aux []]
                [(Term.typeSpec
                  ":"
                  (Term.app
                   `Acc
                   [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
                ":="
                (Term.app `iha [`a₁ `r₁])))
              []
              (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
        (Term.fun
         "fun"
         (Term.basicFun
          [`a₁
           `b₁
           `a₂
           `b₂
           (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`b₁ `b₂])] ")")
           (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
           (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b₂ "=" `xb)] ")")]
          []
          "=>"
          (Term.show
           "show"
           (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
           (Term.fromTerm
            "from"
            (Term.have
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`s₁ []]
               [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
               ":="
               (Term.app `Eq.recOn [`eq₃ `h])))
             []
             (Term.app `ihb [`b₁ `s₁ `a₁]))))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a₁
         `b₁
         `a₂
         `b₂
         (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`b₁ `b₂])] ")")
         (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
         (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b₂ "=" `xb)] ")")]
        []
        "=>"
        (Term.show
         "show"
         (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
         (Term.fromTerm
          "from"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`s₁ []]
             [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
             ":="
             (Term.app `Eq.recOn [`eq₃ `h])))
           []
           (Term.app `ihb [`b₁ `s₁ `a₁]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
       (Term.fromTerm
        "from"
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`s₁ []]
           [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
           ":="
           (Term.app `Eq.recOn [`eq₃ `h])))
         []
         (Term.app `ihb [`b₁ `s₁ `a₁]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`s₁ []]
         [(Term.typeSpec ":" (Term.app `s [`b₁ `xb]))]
         ":="
         (Term.app `Eq.recOn [`eq₃ `h])))
       []
       (Term.app `ihb [`b₁ `s₁ `a₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ihb [`b₁ `s₁ `a₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ihb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.recOn [`eq₃ `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `eq₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `s [`b₁ `xb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.app `mk [`a₁ `b₁])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mk [`a₁ `b₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `mk [`a₁ `b₁]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `RevLex [`r `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RevLex
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `RevLex [`r `s]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Acc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b₂ "=" `xb)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `b₂ "=" `xb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b₂
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq₃ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `a₂ "=" `xa)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq₂ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `s [`b₁ `b₂])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `s [`b₁ `b₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `b₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a₁
         `a₂
         `b
         (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
         (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
         (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b "=" `xb)] ")")]
        []
        "=>"
        (Term.show
         "show"
         (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
         (Term.fromTerm
          "from"
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`r₁ []]
             [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
             ":="
             (Term.app `Eq.recOn [`eq₂ `h])))
           []
           (Term.have
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`aux []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `Acc
                 [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
              ":="
              (Term.app `iha [`a₁ `r₁])))
            []
            (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
       (Term.fromTerm
        "from"
        (Term.have
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`r₁ []]
           [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
           ":="
           (Term.app `Eq.recOn [`eq₂ `h])))
         []
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`aux []]
            [(Term.typeSpec
              ":"
              (Term.app
               `Acc
               [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
            ":="
            (Term.app `iha [`a₁ `r₁])))
          []
          (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`r₁ []]
         [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
         ":="
         (Term.app `Eq.recOn [`eq₂ `h])))
       []
       (Term.have
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`aux []]
          [(Term.typeSpec
            ":"
            (Term.app
             `Acc
             [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
          ":="
          (Term.app `iha [`a₁ `r₁])))
        []
        (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.have
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`aux []]
         [(Term.typeSpec
           ":"
           (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
         ":="
         (Term.app `iha [`a₁ `r₁])))
       []
       (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.recOn [(Term.app `Eq.symm [`eq₃]) `aux])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aux
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Eq.symm [`eq₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Eq.symm [`eq₃]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `iha [`a₁ `r₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `iha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `RevLex [`r `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RevLex
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `RevLex [`r `s]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Acc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.recOn [`eq₂ `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `eq₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `r [`a₁ `xa])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Acc [(Term.app `RevLex [`r `s]) (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `RevLex [`r `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RevLex
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `RevLex [`r `s]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Acc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b "=" `xb)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `b "=" `xb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq₃ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `a₂ "=" `xa)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq₂ [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `r [`a₁ `a₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`a₁
        `a₂
        `b
        (Term.typeAscription "(" (Term.app `h []) ":" [(Term.app `r [`a₁ `a₂])] ")")
        (Term.typeAscription "(" (Term.app `eq₂ []) ":" [(«term_=_» `a₂ "=" `xa)] ")")
        (Term.typeAscription "(" (Term.app `eq₃ []) ":" [(«term_=_» `b "=" `xb)] ")")]
       []
       "=>"
       (Term.show
        "show"
        (Term.app
         `Acc
         [(Term.paren "(" (Term.app `RevLex [`r `s]) ")")
          (Term.anonymousCtor "⟨" [`a₁ "," `b] "⟩")])
        (Term.fromTerm
         "from"
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`r₁ []]
            [(Term.typeSpec ":" (Term.app `r [`a₁ `xa]))]
            ":="
            (Term.app `Eq.recOn [`eq₂ `h])))
          []
          (Term.have
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`aux []]
             [(Term.typeSpec
               ":"
               (Term.app
                `Acc
                [(Term.paren "(" (Term.app `RevLex [`r `s]) ")")
                 (Term.anonymousCtor "⟨" [`a₁ "," `xb] "⟩")]))]
             ":="
             (Term.app `iha [`a₁ `r₁])))
           []
           (Term.app `Eq.recOn [(Term.paren "(" (Term.app `Eq.symm [`eq₃]) ")") `aux])))))))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `lt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p₁ `p₂]
        []
        "=>"
        (Term.arrow
         («term_=_» (Term.app `fst [`p₂]) "=" `xa)
         "→"
         (Term.arrow
          («term_=_» (Term.app `snd [`p₂]) "=" `xb)
          "→"
          (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_=_» (Term.app `fst [`p₂]) "=" `xa)
       "→"
       (Term.arrow
        («term_=_» (Term.app `snd [`p₂]) "=" `xb)
        "→"
        (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_=_» (Term.app `snd [`p₂]) "=" `xb)
       "→"
       (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Acc [(Term.app `RevLex [`r `s]) `p₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `RevLex [`r `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RevLex
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `RevLex [`r `s]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Acc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_=_» (Term.app `snd [`p₂]) "=" `xb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `snd [`p₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `snd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_=_» (Term.app `fst [`p₂]) "=" `xa)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `fst [`p₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`p₁ `p₂]
       []
       "=>"
       (Term.arrow
        («term_=_» (Term.app `fst [`p₂]) "=" `xa)
        "→"
        (Term.arrow
         («term_=_» (Term.app `snd [`p₂]) "=" `xb)
         "→"
         (Term.app `Acc [(Term.paren "(" (Term.app `RevLex [`r `s]) ")") `p₁])))))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `RevLex.rec_on)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RevLex.rec_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_=_» `xa "=" `xa)
       "→"
       (Term.arrow («term_=_» `xb "=" `xb) "→" (Term.app `Acc [(Term.app `RevLex [`r `s]) `p])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow («term_=_» `xb "=" `xb) "→" (Term.app `Acc [(Term.app `RevLex [`r `s]) `p]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Acc [(Term.app `RevLex [`r `s]) `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `RevLex [`r `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RevLex
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `RevLex [`r `s]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Acc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_=_» `xb "=" `xb)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `xb
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_=_» `xa "=" `xa)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `xa
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `lt [])
       ":"
       [(PSigma.Init.Data.Sigma.Lex.«term_≺__1» `p "≺" (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (PSigma.Init.Data.Sigma.Lex.«term_≺__1» `p "≺" (Term.anonymousCtor "⟨" [`xa "," `xb] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'PSigma.Init.Data.Sigma.Lex.«term_≺__1»', expected 'PSigma.Init.Data.Sigma.Lex.term_≺__1._@.Init.Data.Sigma.Lex._hyg.80'
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
theorem
  rev_lex_accessible
  { b } ( acb : Acc s b ) ( aca : ∀ a , Acc r a ) : ∀ a , Acc RevLex r s ⟨ a , b ⟩
  :=
    Acc.recOn
      acb
        fun
          xb acb ( ihb : ∀ y , s y xb → ∀ a , Acc RevLex r s ⟨ a , y ⟩ )
            =>
            fun
              a
                =>
                Acc.recOn
                  aca a
                    fun
                      xa aca ( iha : ∀ y , r y xa → Acc RevLex r s mk y xb )
                        =>
                        Acc.intro
                          ⟨ xa , xb ⟩
                            fun
                              p ( lt : p ≺ ⟨ xa , xb ⟩ )
                                =>
                                have
                                  aux
                                    : xa = xa → xb = xb → Acc RevLex r s p
                                    :=
                                    @ RevLex.rec_on
                                      α
                                        β
                                        r
                                        s
                                        fun p₁ p₂ => fst p₂ = xa → snd p₂ = xb → Acc RevLex r s p₁
                                        p
                                        ⟨ xa , xb ⟩
                                        lt
                                        fun
                                          a₁ a₂ b ( h : r a₁ a₂ ) ( eq₂ : a₂ = xa ) ( eq₃ : b = xb )
                                            =>
                                            show
                                              Acc RevLex r s ⟨ a₁ , b ⟩
                                              from
                                                have
                                                  r₁ : r a₁ xa := Eq.recOn eq₂ h
                                                  have
                                                    aux : Acc RevLex r s ⟨ a₁ , xb ⟩ := iha a₁ r₁
                                                    Eq.recOn Eq.symm eq₃ aux
                                        fun
                                          a₁
                                              b₁
                                              a₂
                                              b₂
                                              ( h : s b₁ b₂ )
                                              ( eq₂ : a₂ = xa )
                                              ( eq₃ : b₂ = xb )
                                            =>
                                            show
                                              Acc RevLex r s mk a₁ b₁
                                              from have s₁ : s b₁ xb := Eq.recOn eq₃ h ihb b₁ s₁ a₁
                                  aux rfl rfl
#align psigma.rev_lex_accessible PSigma.rev_lex_accessible

theorem rev_lex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => rev_lex_accessible (apply hb b) (WellFounded.apply ha) a
#align psigma.rev_lex_wf PSigma.rev_lex_wf

end

section

#print PSigma.SkipLeft /-
def SkipLeft (α : Type u) {β : Type v} (s : β → β → Prop) :
    (@PSigma α fun a => β) → (@PSigma α fun a => β) → Prop :=
  RevLex EmptyRelation s
#align psigma.skip_left PSigma.SkipLeft
-/

theorem skip_left_wf (α : Type u) {β : Type v} {s : β → β → Prop} (hb : WellFounded s) :
    WellFounded (SkipLeft α s) :=
  rev_lex_wf empty_wf hb
#align psigma.skip_left_wf PSigma.skip_left_wf

theorem mk_skip_left {α : Type u} {β : Type v} {b₁ b₂ : β} {s : β → β → Prop} (a₁ a₂ : α)
    (h : s b₁ b₂) : SkipLeft α s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ :=
  RevLex.right _ _ h
#align psigma.mk_skip_left PSigma.mk_skip_left

end

instance hasWellFounded {α : Type u} {β : α → Type v} [s₁ : WellFoundedRelation α]
    [s₂ : ∀ a, WellFoundedRelation (β a)] : WellFoundedRelation (PSigma β)
    where
  R := Lex s₁.R fun a => (s₂ a).R
  wf := lex_wf s₁.wf fun a => (s₂ a).wf
#align psigma.has_well_founded PSigma.hasWellFounded

end PSigma

