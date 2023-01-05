/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.smt.interactive
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Smt.SmtTactic
import Leanbin.Init.Meta.InteractiveBase
import Leanbin.Init.Meta.Smt.Rsimp

namespace SmtTactic

unsafe def save_info (p : Pos) : smt_tactic Unit := do
  let (ss, ts) ← smt_tactic.read
  tactic.save_info_thunk p fun _ => smt_state.to_format ss ts
#align smt_tactic.save_info smt_tactic.save_info

unsafe def skip : smt_tactic Unit :=
  return ()
#align smt_tactic.skip smt_tactic.skip

unsafe def solve_goals : smt_tactic Unit :=
  iterate close
#align smt_tactic.solve_goals smt_tactic.solve_goals

unsafe def step {α : Type} (tac : smt_tactic α) : smt_tactic Unit :=
  tac >> solve_goals
#align smt_tactic.step smt_tactic.step

unsafe def istep {α : Type} (line0 col0 line col ast : Nat) (tac : smt_tactic α) :
    smt_tactic Unit :=
  ⟨fun ss ts =>
    (@scopeTrace _ line col fun _ => tactic.with_ast ast ((tac >> solve_goals).run ss) ts).clamp_pos
      line0 line col⟩
#align smt_tactic.istep smt_tactic.istep

unsafe def execute (tac : smt_tactic Unit) : tactic Unit :=
  using_smt tac
#align smt_tactic.execute smt_tactic.execute

unsafe def execute_with (cfg : SmtConfig) (tac : smt_tactic Unit) : tactic Unit :=
  using_smt tac cfg
#align smt_tactic.execute_with smt_tactic.execute_with

unsafe instance : interactive.executor smt_tactic
    where
  config_type := SmtConfig
  Inhabited := ⟨{ }⟩
  execute_with cfg tac := using_smt tac cfg

namespace Interactive

open Lean.Parser

open _Root_.Interactive

open Interactive.Types

-- mathport name: «expr ?»
local postfix:1024 "?" => optional

-- mathport name: «expr *»
local postfix:1024 "*" => many

unsafe def itactic : Type :=
  smt_tactic Unit
#align smt_tactic.interactive.itactic smt_tactic.interactive.itactic

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [(Command.unsafe "unsafe")] [])
     (Command.def
      "def"
      (Command.declId `intros [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app `parse [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*")])
          "→"
          (Term.app `smt_tactic [`Unit])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" `smt_tactic.intros)
          (Term.matchAlt "|" [[`hs]] "=>" (Term.app `smt_tactic.intro_lst [`hs]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smt_tactic.intro_lst [`hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic.intro_lst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `smt_tactic.intros
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app `parse [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*")])
       "→"
       (Term.app `smt_tactic [`Unit]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smt_tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `parse [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*»', expected 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_*._@.Init.Meta.Smt.Interactive._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
unsafe
  def
    intros
    : parse ident * → smt_tactic Unit
    | [ ] => smt_tactic.intros | hs => smt_tactic.intro_lst hs
#align smt_tactic.interactive.intros smt_tactic.interactive.intros

/-- Try to close main goal by using equalities implied by the congruence
  closure module.
-/
unsafe def close : smt_tactic Unit :=
  smt_tactic.close
#align smt_tactic.interactive.close smt_tactic.interactive.close

/-- Produce new facts using heuristic lemma instantiation based on E-matching.
  This tactic tries to match patterns from lemmas in the main goal with terms
  in the main goal. The set of lemmas is populated with theorems
  tagged with the attribute specified at smt_config.em_attr, and lemmas
  added using tactics such as `smt_tactic.add_lemmas`.
  The current set of lemmas can be retrieved using the tactic `smt_tactic.get_lemmas`.
-/
unsafe def ematch : smt_tactic Unit :=
  smt_tactic.ematch
#align smt_tactic.interactive.ematch smt_tactic.interactive.ematch

unsafe def apply (q : parse texpr) : smt_tactic Unit :=
  tactic.interactive.apply q
#align smt_tactic.interactive.apply smt_tactic.interactive.apply

unsafe def fapply (q : parse texpr) : smt_tactic Unit :=
  tactic.interactive.fapply q
#align smt_tactic.interactive.fapply smt_tactic.interactive.fapply

unsafe def apply_instance : smt_tactic Unit :=
  tactic.apply_instance
#align smt_tactic.interactive.apply_instance smt_tactic.interactive.apply_instance

unsafe def change (q : parse texpr) : smt_tactic Unit :=
  tactic.interactive.change q none (Loc.ns [none])
#align smt_tactic.interactive.change smt_tactic.interactive.change

unsafe def exact (q : parse texpr) : smt_tactic Unit :=
  tactic.interactive.exact q
#align smt_tactic.interactive.exact smt_tactic.interactive.exact

unsafe def from :=
  exact
#align smt_tactic.interactive.from smt_tactic.interactive.from

unsafe def assume :=
  tactic.interactive.assume
#align smt_tactic.interactive.assume smt_tactic.interactive.assume

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [(Command.unsafe "unsafe")] [])
     (Command.def
      "def"
      (Command.declId `have [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.app `parse [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_? `ident "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`q₁]
         [":"
          (Term.app
           `parse
           [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
             («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `texpr)
             "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`q₂]
         [":"
          («term_<|_»
           `parse
           "<|"
           (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
            («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
            "?"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `smt_tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.let
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `h
          []
          []
          ":="
          (Term.app (Term.proj `h "." `getOrElse) [(Term.quotedName (name "`this"))])))
        []
        («term_>>_»
         (Term.match
          "match"
          []
          []
          [(Term.matchDiscr [] `q₁) "," (Term.matchDiscr [] `q₂)]
          "with"
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[(Term.app `some [`e]) "," (Term.app `some [`p])]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `v
                   []
                   "←"
                   (Term.doExpr
                    (Term.app
                     `tactic.to_expr
                     [(Term.precheckedQuot
                       "`"
                       (Term.quot
                        "`("
                        (Term.typeAscription
                         "("
                         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                         ":"
                         [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                         ")")
                        ")"))]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assertv [`h `t `v])) [])])))
            (Term.matchAlt
             "|"
             [[`none "," (Term.app `some [`p])]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.note [`h `none `p])) [])])))
            (Term.matchAlt
             "|"
             [[(Term.app `some [`e]) "," `none]]
             "=>"
             («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.assert [`h])))
            (Term.matchAlt
             "|"
             [[`none "," `none]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `e
                   []
                   "←"
                   (Term.doExpr (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assert [`h `e])) [])])))]))
         ">>"
         (Term.app `return [(Term.tuple "(" [] ")")])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `h
         []
         []
         ":="
         (Term.app (Term.proj `h "." `getOrElse) [(Term.quotedName (name "`this"))])))
       []
       («term_>>_»
        (Term.match
         "match"
         []
         []
         [(Term.matchDiscr [] `q₁) "," (Term.matchDiscr [] `q₂)]
         "with"
         (Term.matchAlts
          [(Term.matchAlt
            "|"
            [[(Term.app `some [`e]) "," (Term.app `some [`p])]]
            "=>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
                [])
               (Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl
                  `v
                  []
                  "←"
                  (Term.doExpr
                   (Term.app
                    `tactic.to_expr
                    [(Term.precheckedQuot
                      "`"
                      (Term.quot
                       "`("
                       (Term.typeAscription
                        "("
                        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                        ":"
                        [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                        ")")
                       ")"))]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assertv [`h `t `v])) [])])))
           (Term.matchAlt
            "|"
            [[`none "," (Term.app `some [`p])]]
            "=>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.note [`h `none `p])) [])])))
           (Term.matchAlt
            "|"
            [[(Term.app `some [`e]) "," `none]]
            "=>"
            («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.assert [`h])))
           (Term.matchAlt
            "|"
            [[`none "," `none]]
            "=>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
                [])
               (Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl
                  `e
                  []
                  "←"
                  (Term.doExpr (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assert [`h `e])) [])])))]))
        ">>"
        (Term.app `return [(Term.tuple "(" [] ")")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_»
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `q₁) "," (Term.matchDiscr [] `q₂)]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.app `some [`e]) "," (Term.app `some [`p])]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl
                 `v
                 []
                 "←"
                 (Term.doExpr
                  (Term.app
                   `tactic.to_expr
                   [(Term.precheckedQuot
                     "`"
                     (Term.quot
                      "`("
                      (Term.typeAscription
                       "("
                       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                       ":"
                       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                       ")")
                      ")"))]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assertv [`h `t `v])) [])])))
          (Term.matchAlt
           "|"
           [[`none "," (Term.app `some [`p])]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.note [`h `none `p])) [])])))
          (Term.matchAlt
           "|"
           [[(Term.app `some [`e]) "," `none]]
           "=>"
           («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.assert [`h])))
          (Term.matchAlt
           "|"
           [[`none "," `none]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl
                 `e
                 []
                 "←"
                 (Term.doExpr (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assert [`h `e])) [])])))]))
       ">>"
       (Term.app `return [(Term.tuple "(" [] ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `return [(Term.tuple "(" [] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `q₁) "," (Term.matchDiscr [] `q₂)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `some [`e]) "," (Term.app `some [`p])]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl
                `v
                []
                "←"
                (Term.doExpr
                 (Term.app
                  `tactic.to_expr
                  [(Term.precheckedQuot
                    "`"
                    (Term.quot
                     "`("
                     (Term.typeAscription
                      "("
                      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                      ":"
                      [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                      ")")
                     ")"))]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assertv [`h `t `v])) [])])))
         (Term.matchAlt
          "|"
          [[`none "," (Term.app `some [`p])]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.note [`h `none `p])) [])])))
         (Term.matchAlt
          "|"
          [[(Term.app `some [`e]) "," `none]]
          "=>"
          («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.assert [`h])))
         (Term.matchAlt
          "|"
          [[`none "," `none]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl
                `e
                []
                "←"
                (Term.doExpr (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assert [`h `e])) [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `e
            []
            "←"
            (Term.doExpr (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assert [`h `e])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smt_tactic.assert [`h `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic.assert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `expr.sort [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `expr.sort
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `expr.sort [`u]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.mk_meta_var
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `tactic.mk_meta_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.assert [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smt_tactic.assert [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic.assert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `tactic.to_expr [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 55, (some 56,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.note [`h `none `p])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smt_tactic.note [`h `none `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `none
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic.note
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `tactic.to_expr [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `v
            []
            "←"
            (Term.doExpr
             (Term.app
              `tactic.to_expr
              [(Term.precheckedQuot
                "`"
                (Term.quot
                 "`("
                 (Term.typeAscription
                  "("
                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                  ":"
                  [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                  ")")
                 ")"))]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assertv [`h `t `v])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smt_tactic.assertv [`h `t `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic.assertv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `tactic.to_expr
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.typeAscription
           "("
           (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
           ":"
           [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
           ")")
          ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.precheckedQuot
       "`"
       (Term.quot
        "`("
        (Term.typeAscription
         "("
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
         ":"
         [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
         ")")
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
       ":"
       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `tactic.to_expr [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 0, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.match
      "match"
      []
      []
      [(Term.matchDiscr [] `q₁) "," (Term.matchDiscr [] `q₂)]
      "with"
      (Term.matchAlts
       [(Term.matchAlt
         "|"
         [[(Term.app `some [`e]) "," (Term.app `some [`p])]]
         "=>"
         (Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
             [])
            (Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl
               `v
               []
               "←"
               (Term.doExpr
                (Term.app
                 `tactic.to_expr
                 [(Term.precheckedQuot
                   "`"
                   (Term.quot
                    "`("
                    (Term.typeAscription
                     "("
                     (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                     ":"
                     [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                     ")")
                    ")"))]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assertv [`h `t `v])) [])])))
        (Term.matchAlt
         "|"
         [[`none "," (Term.app `some [`p])]]
         "=>"
         (Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.note [`h `none `p])) [])])))
        (Term.matchAlt
         "|"
         [[(Term.app `some [`e]) "," `none]]
         "=>"
         («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.assert [`h])))
        (Term.matchAlt
         "|"
         [[`none "," `none]]
         "=>"
         (Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
             [])
            (Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl
               `e
               []
               "←"
               (Term.doExpr
                (Term.app `tactic.mk_meta_var [(Term.paren "(" (Term.app `expr.sort [`u]) ")")]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.assert [`h `e])) [])])))]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `h "." `getOrElse) [(Term.quotedName (name "`this"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`this"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `h "." `getOrElse)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `smt_tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `parse
       "<|"
       (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
        («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
        "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
       («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
       "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?', expected 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?._@.Init.Meta.Smt.Interactive._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
unsafe
  def
    have
    ( h : parse ident ? ) ( q₁ : parse tk ":" *> texpr ? ) ( q₂ : parse <| tk ":=" *> texpr ? )
      : smt_tactic Unit
    :=
      let
        h := h . getOrElse `this
        match
            q₁ , q₂
            with
            |
                some e , some p
                =>
                do
                  let t ← tactic.to_expr e
                    let v ← tactic.to_expr ` `( ( $ ( p ) : $ ( t ) ) )
                    smt_tactic.assertv h t v
              | none , some p => do let p ← tactic.to_expr p smt_tactic.note h none p
              | some e , none => tactic.to_expr e >>= smt_tactic.assert h
              |
                none , none
                =>
                do
                  let u ← tactic.mk_meta_univ
                    let e ← tactic.mk_meta_var expr.sort u
                    smt_tactic.assert h e
          >>
          return ( )
#align smt_tactic.interactive.have smt_tactic.interactive.have

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [(Command.unsafe "unsafe")] [])
     (Command.def
      "def"
      (Command.declId `let [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.app `parse [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_? `ident "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`q₁]
         [":"
          (Term.app
           `parse
           [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
             («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `texpr)
             "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`q₂]
         [":"
          («term_<|_»
           `parse
           "<|"
           (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
            («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
            "?"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `smt_tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.let
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `h
          []
          []
          ":="
          (Term.app (Term.proj `h "." `getOrElse) [(Term.quotedName (name "`this"))])))
        []
        («term_>>_»
         (Term.match
          "match"
          []
          []
          [(Term.matchDiscr [] `q₁) "," (Term.matchDiscr [] `q₂)]
          "with"
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[(Term.app `some [`e]) "," (Term.app `some [`p])]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `v
                   []
                   "←"
                   (Term.doExpr
                    (Term.app
                     `tactic.to_expr
                     [(Term.precheckedQuot
                       "`"
                       (Term.quot
                        "`("
                        (Term.typeAscription
                         "("
                         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                         ":"
                         [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                         ")")
                        ")"))]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.definev [`h `t `v])) [])])))
            (Term.matchAlt
             "|"
             [[`none "," (Term.app `some [`p])]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.pose [`h `none `p])) [])])))
            (Term.matchAlt
             "|"
             [[(Term.app `some [`e]) "," `none]]
             "=>"
             («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.define [`h])))
            (Term.matchAlt
             "|"
             [[`none "," `none]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `e
                   []
                   "←"
                   (Term.doExpr (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.define [`h `e])) [])])))]))
         ">>"
         (Term.app `return [(Term.tuple "(" [] ")")])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `h
         []
         []
         ":="
         (Term.app (Term.proj `h "." `getOrElse) [(Term.quotedName (name "`this"))])))
       []
       («term_>>_»
        (Term.match
         "match"
         []
         []
         [(Term.matchDiscr [] `q₁) "," (Term.matchDiscr [] `q₂)]
         "with"
         (Term.matchAlts
          [(Term.matchAlt
            "|"
            [[(Term.app `some [`e]) "," (Term.app `some [`p])]]
            "=>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
                [])
               (Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl
                  `v
                  []
                  "←"
                  (Term.doExpr
                   (Term.app
                    `tactic.to_expr
                    [(Term.precheckedQuot
                      "`"
                      (Term.quot
                       "`("
                       (Term.typeAscription
                        "("
                        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                        ":"
                        [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                        ")")
                       ")"))]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.definev [`h `t `v])) [])])))
           (Term.matchAlt
            "|"
            [[`none "," (Term.app `some [`p])]]
            "=>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.pose [`h `none `p])) [])])))
           (Term.matchAlt
            "|"
            [[(Term.app `some [`e]) "," `none]]
            "=>"
            («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.define [`h])))
           (Term.matchAlt
            "|"
            [[`none "," `none]]
            "=>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
                [])
               (Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl
                  `e
                  []
                  "←"
                  (Term.doExpr (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.define [`h `e])) [])])))]))
        ">>"
        (Term.app `return [(Term.tuple "(" [] ")")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_»
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `q₁) "," (Term.matchDiscr [] `q₂)]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.app `some [`e]) "," (Term.app `some [`p])]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl
                 `v
                 []
                 "←"
                 (Term.doExpr
                  (Term.app
                   `tactic.to_expr
                   [(Term.precheckedQuot
                     "`"
                     (Term.quot
                      "`("
                      (Term.typeAscription
                       "("
                       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                       ":"
                       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                       ")")
                      ")"))]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.definev [`h `t `v])) [])])))
          (Term.matchAlt
           "|"
           [[`none "," (Term.app `some [`p])]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.pose [`h `none `p])) [])])))
          (Term.matchAlt
           "|"
           [[(Term.app `some [`e]) "," `none]]
           "=>"
           («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.define [`h])))
          (Term.matchAlt
           "|"
           [[`none "," `none]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl
                 `e
                 []
                 "←"
                 (Term.doExpr (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.define [`h `e])) [])])))]))
       ">>"
       (Term.app `return [(Term.tuple "(" [] ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `return [(Term.tuple "(" [] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `q₁) "," (Term.matchDiscr [] `q₂)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `some [`e]) "," (Term.app `some [`p])]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl
                `v
                []
                "←"
                (Term.doExpr
                 (Term.app
                  `tactic.to_expr
                  [(Term.precheckedQuot
                    "`"
                    (Term.quot
                     "`("
                     (Term.typeAscription
                      "("
                      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                      ":"
                      [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                      ")")
                     ")"))]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.definev [`h `t `v])) [])])))
         (Term.matchAlt
          "|"
          [[`none "," (Term.app `some [`p])]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.pose [`h `none `p])) [])])))
         (Term.matchAlt
          "|"
          [[(Term.app `some [`e]) "," `none]]
          "=>"
          («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.define [`h])))
         (Term.matchAlt
          "|"
          [[`none "," `none]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl
                `e
                []
                "←"
                (Term.doExpr (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.define [`h `e])) [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `e
            []
            "←"
            (Term.doExpr (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.define [`h `e])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smt_tactic.define [`h `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic.define
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `tactic.mk_meta_var [(Term.app `expr.sort [`u])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `expr.sort [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `expr.sort
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `expr.sort [`u]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.mk_meta_var
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `tactic.mk_meta_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.define [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smt_tactic.define [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic.define
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `tactic.to_expr [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 55, (some 56,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.pose [`h `none `p])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smt_tactic.pose [`h `none `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `none
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic.pose
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `tactic.to_expr [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `v
            []
            "←"
            (Term.doExpr
             (Term.app
              `tactic.to_expr
              [(Term.precheckedQuot
                "`"
                (Term.quot
                 "`("
                 (Term.typeAscription
                  "("
                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                  ":"
                  [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                  ")")
                 ")"))]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.definev [`h `t `v])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smt_tactic.definev [`h `t `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic.definev
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `tactic.to_expr
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.typeAscription
           "("
           (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
           ":"
           [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
           ")")
          ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.precheckedQuot
       "`"
       (Term.quot
        "`("
        (Term.typeAscription
         "("
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
         ":"
         [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
         ")")
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
       ":"
       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `tactic.to_expr [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 0, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.match
      "match"
      []
      []
      [(Term.matchDiscr [] `q₁) "," (Term.matchDiscr [] `q₂)]
      "with"
      (Term.matchAlts
       [(Term.matchAlt
         "|"
         [[(Term.app `some [`e]) "," (Term.app `some [`p])]]
         "=>"
         (Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `tactic.to_expr [`e]))))
             [])
            (Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl
               `v
               []
               "←"
               (Term.doExpr
                (Term.app
                 `tactic.to_expr
                 [(Term.precheckedQuot
                   "`"
                   (Term.quot
                    "`("
                    (Term.typeAscription
                     "("
                     (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `p ")") [])
                     ":"
                     [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])]
                     ")")
                    ")"))]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.definev [`h `t `v])) [])])))
        (Term.matchAlt
         "|"
         [[`none "," (Term.app `some [`p])]]
         "=>"
         (Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `tactic.to_expr [`p]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.pose [`h `none `p])) [])])))
        (Term.matchAlt
         "|"
         [[(Term.app `some [`e]) "," `none]]
         "=>"
         («term_>>=_» (Term.app `tactic.to_expr [`e]) ">>=" (Term.app `smt_tactic.define [`h])))
        (Term.matchAlt
         "|"
         [[`none "," `none]]
         "=>"
         (Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `tactic.mk_meta_univ)))
             [])
            (Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl
               `e
               []
               "←"
               (Term.doExpr
                (Term.app `tactic.mk_meta_var [(Term.paren "(" (Term.app `expr.sort [`u]) ")")]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `smt_tactic.define [`h `e])) [])])))]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `h "." `getOrElse) [(Term.quotedName (name "`this"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`this"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `h "." `getOrElse)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `smt_tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `parse
       "<|"
       (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
        («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
        "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
       («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
       "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?', expected 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?._@.Init.Meta.Smt.Interactive._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
unsafe
  def
    let
    ( h : parse ident ? ) ( q₁ : parse tk ":" *> texpr ? ) ( q₂ : parse <| tk ":=" *> texpr ? )
      : smt_tactic Unit
    :=
      let
        h := h . getOrElse `this
        match
            q₁ , q₂
            with
            |
                some e , some p
                =>
                do
                  let t ← tactic.to_expr e
                    let v ← tactic.to_expr ` `( ( $ ( p ) : $ ( t ) ) )
                    smt_tactic.definev h t v
              | none , some p => do let p ← tactic.to_expr p smt_tactic.pose h none p
              | some e , none => tactic.to_expr e >>= smt_tactic.define h
              |
                none , none
                =>
                do
                  let u ← tactic.mk_meta_univ
                    let e ← tactic.mk_meta_var expr.sort u
                    smt_tactic.define h e
          >>
          return ( )
#align smt_tactic.interactive.let smt_tactic.interactive.let

unsafe def add_fact (q : parse texpr) : smt_tactic Unit := do
  let h ← tactic.get_unused_name `h none
  let p ← tactic.to_expr_strict q
  smt_tactic.note h none p
#align smt_tactic.interactive.add_fact smt_tactic.interactive.add_fact

unsafe def trace_state : smt_tactic Unit :=
  smt_tactic.trace_state
#align smt_tactic.interactive.trace_state smt_tactic.interactive.trace_state

unsafe def trace {α : Type} [has_to_tactic_format α] (a : α) : smt_tactic Unit :=
  tactic.trace a
#align smt_tactic.interactive.trace smt_tactic.interactive.trace

unsafe def destruct (q : parse texpr) : smt_tactic Unit := do
  let p ← tactic.to_expr_strict q
  smt_tactic.destruct p
#align smt_tactic.interactive.destruct smt_tactic.interactive.destruct

unsafe def by_cases (q : parse texpr) : smt_tactic Unit := do
  let p ← tactic.to_expr_strict q
  smt_tactic.by_cases p
#align smt_tactic.interactive.by_cases smt_tactic.interactive.by_cases

unsafe def by_contradiction : smt_tactic Unit :=
  smt_tactic.by_contradiction
#align smt_tactic.interactive.by_contradiction smt_tactic.interactive.by_contradiction

unsafe def by_contra : smt_tactic Unit :=
  smt_tactic.by_contradiction
#align smt_tactic.interactive.by_contra smt_tactic.interactive.by_contra

open Tactic (resolve_name Transparency to_expr)

private unsafe def report_invalid_em_lemma {α : Type} (n : Name) : smt_tactic α :=
  fail f! "invalid ematch lemma '{n}'"
#align smt_tactic.interactive.report_invalid_em_lemma smt_tactic.interactive.report_invalid_em_lemma

private unsafe def add_lemma_name (md : Transparency) (lhs_lemma : Bool) (n : Name) (ref : pexpr) :
    smt_tactic Unit := do
  let p ← resolve_name n
  match p with
    | expr.const n _ =>
      add_ematch_lemma_from_decl_core md lhs_lemma n >> tactic.save_const_type_info n ref <|>
        report_invalid_em_lemma n
    | _ =>
      (do
          let e ← to_expr p
          add_ematch_lemma_core md lhs_lemma e >> try (tactic.save_type_info e ref)) <|>
        report_invalid_em_lemma n
#align smt_tactic.interactive.add_lemma_name smt_tactic.interactive.add_lemma_name

private unsafe def add_lemma_pexpr (md : Transparency) (lhs_lemma : Bool) (p : pexpr) :
    smt_tactic Unit :=
  match p with
  | expr.const c [] => add_lemma_name md lhs_lemma c p
  | expr.local_const c _ _ _ => add_lemma_name md lhs_lemma c p
  | _ => do
    let new_e ← to_expr p
    add_ematch_lemma_core md lhs_lemma new_e
#align smt_tactic.interactive.add_lemma_pexpr smt_tactic.interactive.add_lemma_pexpr

private unsafe def add_lemma_pexprs (md : Transparency) (lhs_lemma : Bool) :
    List pexpr → smt_tactic Unit
  | [] => return ()
  | p :: ps => add_lemma_pexpr md lhs_lemma p >> add_lemma_pexprs ps
#align smt_tactic.interactive.add_lemma_pexprs smt_tactic.interactive.add_lemma_pexprs

unsafe def add_lemma (l : parse pexpr_list_or_texpr) : smt_tactic Unit :=
  add_lemma_pexprs reducible false l
#align smt_tactic.interactive.add_lemma smt_tactic.interactive.add_lemma

unsafe def add_lhs_lemma (l : parse pexpr_list_or_texpr) : smt_tactic Unit :=
  add_lemma_pexprs reducible true l
#align smt_tactic.interactive.add_lhs_lemma smt_tactic.interactive.add_lhs_lemma

private unsafe def add_eqn_lemmas_for_core (md : Transparency) : List Name → smt_tactic Unit
  | [] => return ()
  | c :: cs => do
    let p ← resolve_name c
    match p with
      | expr.const n _ => add_ematch_eqn_lemmas_for_core md n >> add_eqn_lemmas_for_core cs
      | _ => fail f! "'{c}' is not a constant"
#align smt_tactic.interactive.add_eqn_lemmas_for_core smt_tactic.interactive.add_eqn_lemmas_for_core

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [(Command.unsafe "unsafe")] [])
     (Command.def
      "def"
      (Command.declId `add_eqn_lemmas_for [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`ids]
         [":"
          (Term.app `parse [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `smt_tactic [`Unit]))])
      (Command.declValSimple ":=" (Term.app `add_eqn_lemmas_for_core [`reducible `ids]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_eqn_lemmas_for_core [`reducible `ids])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ids
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `reducible
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_eqn_lemmas_for_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `smt_tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*»', expected 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_*._@.Init.Meta.Smt.Interactive._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
unsafe
  def
    add_eqn_lemmas_for
    ( ids : parse ident * ) : smt_tactic Unit
    := add_eqn_lemmas_for_core reducible ids
#align smt_tactic.interactive.add_eqn_lemmas_for smt_tactic.interactive.add_eqn_lemmas_for

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [(Command.unsafe "unsafe")] [])
     (Command.def
      "def"
      (Command.declId `add_eqn_lemmas [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`ids]
         [":"
          (Term.app `parse [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `smt_tactic [`Unit]))])
      (Command.declValSimple ":=" (Term.app `add_eqn_lemmas_for [`ids]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_eqn_lemmas_for [`ids])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ids
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_eqn_lemmas_for
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `smt_tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [(SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*»', expected 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_*._@.Init.Meta.Smt.Interactive._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
unsafe def add_eqn_lemmas ( ids : parse ident * ) : smt_tactic Unit := add_eqn_lemmas_for ids
#align smt_tactic.interactive.add_eqn_lemmas smt_tactic.interactive.add_eqn_lemmas

private unsafe def add_hinst_lemma_from_name (md : Transparency) (lhs_lemma : Bool) (n : Name)
    (hs : hinst_lemmas) (ref : pexpr) : smt_tactic hinst_lemmas := do
  let p ← resolve_name n
  match p with
    | expr.const n _ =>
      (do
          let h ← hinst_lemma.mk_from_decl_core md n lhs_lemma
          tactic.save_const_type_info n ref
          return <| hs h) <|>
        (do
            let hs₁ ← mk_ematch_eqn_lemmas_for_core md n
            tactic.save_const_type_info n ref
            return <| hs hs₁) <|>
          report_invalid_em_lemma n
    | _ =>
      (do
          let e ← to_expr p
          let h ← hinst_lemma.mk_core md e lhs_lemma
          try (tactic.save_type_info e ref)
          return <| hs h) <|>
        report_invalid_em_lemma n
#align
  smt_tactic.interactive.add_hinst_lemma_from_name smt_tactic.interactive.add_hinst_lemma_from_name

private unsafe def add_hinst_lemma_from_pexpr (md : Transparency) (lhs_lemma : Bool) (p : pexpr)
    (hs : hinst_lemmas) : smt_tactic hinst_lemmas :=
  match p with
  | expr.const c [] => add_hinst_lemma_from_name md lhs_lemma c hs p
  | expr.local_const c _ _ _ => add_hinst_lemma_from_name md lhs_lemma c hs p
  | _ => do
    let new_e ← to_expr p
    let h ← hinst_lemma.mk_core md new_e lhs_lemma
    return <| hs h
#align
  smt_tactic.interactive.add_hinst_lemma_from_pexpr smt_tactic.interactive.add_hinst_lemma_from_pexpr

private unsafe def add_hinst_lemmas_from_pexprs (md : Transparency) (lhs_lemma : Bool) :
    List pexpr → hinst_lemmas → smt_tactic hinst_lemmas
  | [], hs => return hs
  | p :: ps, hs => do
    let hs₁ ← add_hinst_lemma_from_pexpr md lhs_lemma p hs
    add_hinst_lemmas_from_pexprs ps hs₁
#align
  smt_tactic.interactive.add_hinst_lemmas_from_pexprs smt_tactic.interactive.add_hinst_lemmas_from_pexprs

unsafe def ematch_using (l : parse pexpr_list_or_texpr) : smt_tactic Unit := do
  let hs ← add_hinst_lemmas_from_pexprs reducible false l hinst_lemmas.mk
  smt_tactic.ematch_using hs
#align smt_tactic.interactive.ematch_using smt_tactic.interactive.ematch_using

/-- Try the given tactic, and do nothing if it fails. -/
unsafe def try (t : itactic) : smt_tactic Unit :=
  smt_tactic.try t
#align smt_tactic.interactive.try smt_tactic.interactive.try

/-- Keep applying the given tactic until it fails. -/
unsafe def iterate (t : itactic) : smt_tactic Unit :=
  smt_tactic.iterate t
#align smt_tactic.interactive.iterate smt_tactic.interactive.iterate

/-- Apply the given tactic to all remaining goals. -/
unsafe def all_goals (t : itactic) : smt_tactic Unit :=
  smt_tactic.all_goals t
#align smt_tactic.interactive.all_goals smt_tactic.interactive.all_goals

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [(Command.unsafe "unsafe")] [])
     (Command.def
      "def"
      (Command.declId `induction [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`p]
         [":" (Term.app `parse [`tactic.interactive.cases_arg_p])]
         []
         ")")
        (Term.explicitBinder "(" [`rec_name] [":" (Term.app `parse [`using_ident])] [] ")")
        (Term.explicitBinder "(" [`ids] [":" (Term.app `parse [`with_ident_list])] [] ")")
        (Term.explicitBinder
         "("
         [`revert]
         [":"
          («term_<|_»
           `parse
           "<|"
           (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
            («term_*>_»
             (Term.app `tk [(str "\"generalizing\"")])
             "*>"
             (SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*"))
            "?"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `smt_tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.app `slift [(Term.app `tactic.interactive.induction [`p `rec_name `ids `revert])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `slift [(Term.app `tactic.interactive.induction [`p `rec_name `ids `revert])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.interactive.induction [`p `rec_name `ids `revert])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `revert
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ids
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `rec_name
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.interactive.induction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `tactic.interactive.induction [`p `rec_name `ids `revert])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `slift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `smt_tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `parse
       "<|"
       (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
        («term_*>_»
         (Term.app `tk [(str "\"generalizing\"")])
         "*>"
         (SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*"))
        "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
       («term_*>_»
        (Term.app `tk [(str "\"generalizing\"")])
        "*>"
        (SmtTactic.Interactive.Init.Meta.Smt.Interactive.«term_*» `ident "*"))
       "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?', expected 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?._@.Init.Meta.Smt.Interactive._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
unsafe
  def
    induction
    ( p : parse tactic.interactive.cases_arg_p )
        ( rec_name : parse using_ident )
        ( ids : parse with_ident_list )
        ( revert : parse <| tk "generalizing" *> ident * ? )
      : smt_tactic Unit
    := slift tactic.interactive.induction p rec_name ids revert
#align smt_tactic.interactive.induction smt_tactic.interactive.induction

open Tactic

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Simplify the target type of the main goal. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `simp [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`use_iota_eqn]
         [":"
          («term_<|_»
           `parse
           "<|"
           (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?
            (Term.app `tk [(str "\"!\"")])
            "?"))]
         []
         ")")
        (Term.explicitBinder "(" [`no_dflt] [":" (Term.app `parse [`only_flag])] [] ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `parse [`simp_arg_list])] [] ")")
        (Term.explicitBinder "(" [`attr_names] [":" (Term.app `parse [`with_ident_list])] [] ")")
        (Term.explicitBinder
         "("
         [`cfg]
         [":" `simp_config_ext]
         [(Term.binderDefault ":=" (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}"))]
         ")")]
       [(Term.typeSpec ":" (Term.app `smt_tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.app
        `tactic.interactive.simp
        [`use_iota_eqn
         `none
         `no_dflt
         `hs
         `attr_names
         (Term.app `Loc.ns [(«term[_]» "[" [`none] "]")])
         `cfg])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tactic.interactive.simp
       [`use_iota_eqn
        `none
        `no_dflt
        `hs
        `attr_names
        (Term.app `Loc.ns [(«term[_]» "[" [`none] "]")])
        `cfg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Loc.ns [(«term[_]» "[" [`none] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`none] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Loc.ns
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Loc.ns [(«term[_]» "[" [`none] "]")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `attr_names
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `no_dflt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `none
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `use_iota_eqn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.interactive.simp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `smt_tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smt_tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.binderDefault', expected 'Lean.Parser.Term.binderTactic'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simp_config_ext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [`with_ident_list])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `with_ident_list
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `parse
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [`simp_arg_list])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `simp_arg_list
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `parse
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [`only_flag])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `only_flag
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `parse
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `parse
       "<|"
       (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_? (Term.app `tk [(str "\"!\"")]) "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_? (Term.app `tk [(str "\"!\"")]) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?', expected 'SmtTactic.Interactive.Init.Meta.Smt.Interactive.term_?._@.Init.Meta.Smt.Interactive._hyg.12'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Simplify the target type of the main goal. -/ unsafe
  def
    simp
    ( use_iota_eqn : parse <| tk "!" ? )
        ( no_dflt : parse only_flag )
        ( hs : parse simp_arg_list )
        ( attr_names : parse with_ident_list )
        ( cfg : simp_config_ext := { } )
      : smt_tactic Unit
    := tactic.interactive.simp use_iota_eqn none no_dflt hs attr_names Loc.ns [ none ] cfg
#align smt_tactic.interactive.simp smt_tactic.interactive.simp

unsafe def dsimp (no_dflt : parse only_flag) (es : parse simp_arg_list)
    (attr_names : parse with_ident_list) : smt_tactic Unit :=
  tactic.interactive.dsimp no_dflt es attr_names (Loc.ns [none])
#align smt_tactic.interactive.dsimp smt_tactic.interactive.dsimp

unsafe def rsimp : smt_tactic Unit := do
  let ccs ← to_cc_state
  _root_.rsimp.rsimplify_goal ccs
#align smt_tactic.interactive.rsimp smt_tactic.interactive.rsimp

unsafe def add_simp_lemmas : smt_tactic Unit :=
  get_hinst_lemmas_for_attr `rsimp_attr >>= add_lemmas
#align smt_tactic.interactive.add_simp_lemmas smt_tactic.interactive.add_simp_lemmas

/-- Keep applying heuristic instantiation until the current goal is solved, or it fails. -/
unsafe def eblast : smt_tactic Unit :=
  smt_tactic.eblast
#align smt_tactic.interactive.eblast smt_tactic.interactive.eblast

/--
Keep applying heuristic instantiation using the given lemmas until the current goal is solved, or it fails. -/
unsafe def eblast_using (l : parse pexpr_list_or_texpr) : smt_tactic Unit := do
  let hs ← add_hinst_lemmas_from_pexprs reducible false l hinst_lemmas.mk
  smt_tactic.iterate (smt_tactic.ematch_using hs >> smt_tactic.try smt_tactic.close)
#align smt_tactic.interactive.eblast_using smt_tactic.interactive.eblast_using

unsafe def guard_expr_eq (t : expr) (p : parse <| tk ":=" *> texpr) : smt_tactic Unit := do
  let e ← to_expr p
  guard (expr.alpha_eqv t e)
#align smt_tactic.interactive.guard_expr_eq smt_tactic.interactive.guard_expr_eq

unsafe def guard_target (p : parse texpr) : smt_tactic Unit := do
  let t ← target
  guard_expr_eq t p
#align smt_tactic.interactive.guard_target smt_tactic.interactive.guard_target

end Interactive

end SmtTactic

