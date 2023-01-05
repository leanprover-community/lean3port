/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module data.dlist
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

universe u

/-- A difference list is a function that, given a list, returns the original
contents of the difference list prepended to the given list.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/
structure Dlist (α : Type u) where
  apply : List α → List α
  invariant : ∀ l, apply l = apply [] ++ l
#align dlist Dlist

namespace Dlist

open Function

variable {α : Type u}

-- mathport name: «expr♯»
local notation:arg "♯" => by abstract intros ; simp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Convert a list to a dlist -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `ofList [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`l] [":" (Term.app `List [`α])] [] ")")]
       [(Term.typeSpec ":" (Term.app `Dlist [`α]))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor "⟨" [(Term.app `append [`l]) "," (Dlist.Data.Dlist.«term♯» "♯")] "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `append [`l]) "," (Dlist.Data.Dlist.«term♯» "♯")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Dlist.Data.Dlist.«term♯» "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Dlist.Data.Dlist.«term♯»', expected 'Dlist.Data.Dlist.term♯._@.Data.Dlist._hyg.7'
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
/-- Convert a list to a dlist -/ def ofList ( l : List α ) : Dlist α := ⟨ append l , ♯ ⟩
#align dlist.of_list Dlist.ofList

/- warning: dlist.lazy_of_list -> Std.DList.lazy_ofList is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, (Thunkₓ.{u1} (List.{u1} α)) -> (Dlist.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, (Thunk.{u1} (List.{u1} α)) -> (Std.DList.{u1} α)
Case conversion may be inaccurate. Consider using '#align dlist.lazy_of_list Std.DList.lazy_ofListₓ'. -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Convert a lazily-evaluated list to a dlist -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `Std.DList.lazy_ofList [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`l] [":" (Term.app `Thunk [(Term.app `List [`α])])] [] ")")]
       [(Term.typeSpec ":" (Term.app `Dlist [`α]))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`xs]
           []
           "=>"
           («term_++_» (Term.app `l [(Term.tuple "(" [] ")")]) "++" `xs)))
         ","
         (Dlist.Data.Dlist.«term♯» "♯")]
        "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`xs]
          []
          "=>"
          («term_++_» (Term.app `l [(Term.tuple "(" [] ")")]) "++" `xs)))
        ","
        (Dlist.Data.Dlist.«term♯» "♯")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Dlist.Data.Dlist.«term♯» "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Dlist.Data.Dlist.«term♯»', expected 'Dlist.Data.Dlist.term♯._@.Data.Dlist._hyg.7'
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
/-- Convert a lazily-evaluated list to a dlist -/
  def Std.DList.lazy_ofList ( l : Thunk List α ) : Dlist α := ⟨ fun xs => l ( ) ++ xs , ♯ ⟩
#align dlist.lazy_of_list Std.DList.lazy_ofList

/-- Convert a dlist to a list -/
def toList : Dlist α → List α
  | ⟨xs, _⟩ => xs []
#align dlist.to_list Dlist.toList

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Create a dlist containing no elements -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `empty [])
      (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Dlist [`α]))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor "⟨" [`id "," (Dlist.Data.Dlist.«term♯» "♯")] "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`id "," (Dlist.Data.Dlist.«term♯» "♯")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Dlist.Data.Dlist.«term♯» "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Dlist.Data.Dlist.«term♯»', expected 'Dlist.Data.Dlist.term♯._@.Data.Dlist._hyg.7'
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
/-- Create a dlist containing no elements -/ def empty : Dlist α := ⟨ id , ♯ ⟩
#align dlist.empty Dlist.empty

-- mathport name: «expr ::_»
local notation:arg a "::_" => List.cons a

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Create dlist with a single element -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `singleton [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" `α] [] ")")]
       [(Term.typeSpec ":" (Term.app `Dlist [`α]))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Dlist.Data.Dlist.«term_::_» `x "::_") "," (Dlist.Data.Dlist.«term♯» "♯")]
        "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Dlist.Data.Dlist.«term_::_» `x "::_") "," (Dlist.Data.Dlist.«term♯» "♯")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Dlist.Data.Dlist.«term♯» "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Dlist.Data.Dlist.«term♯»', expected 'Dlist.Data.Dlist.term♯._@.Data.Dlist._hyg.7'
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
/-- Create dlist with a single element -/ def singleton ( x : α ) : Dlist α := ⟨ x ::_ , ♯ ⟩
#align dlist.singleton Dlist.singleton

attribute [local simp] Function.comp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "`O(1)` Prepend a single element to a dlist -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `cons [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" `α] [] ")")]
       [(Term.typeSpec ":" (Term.arrow (Term.app `Dlist [`α]) "→" (Term.app `Dlist [`α])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.anonymousCtor "⟨" [`xs "," `h] "⟩")]]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(«term_∘_» (Dlist.Data.Dlist.«term_::_» `x "::_") "∘" `xs)
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.abstract
                  "abstract"
                  []
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.intros "intros" [])
                     ";"
                     (Tactic.simp "simp" [] [] [] [] [])
                     ";"
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)]
                       "]")
                      [])])))])))]
            "⟩"))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_∘_» (Dlist.Data.Dlist.«term_::_» `x "::_") "∘" `xs)
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.abstract
             "abstract"
             []
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.intros "intros" [])
                ";"
                (Tactic.simp "simp" [] [] [] [] [])
                ";"
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
                 [])])))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.abstract
           "abstract"
           []
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.intros "intros" [])
              ";"
              (Tactic.simp "simp" [] [] [] [] [])
              ";"
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
               [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.abstract
       "abstract"
       []
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intros "intros" [])
          ";"
          (Tactic.simp "simp" [] [] [] [] [])
          ";"
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `h)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Dlist.Data.Dlist.«term_::_» `x "::_") "∘" `xs)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xs
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Dlist.Data.Dlist.«term_::_» `x "::_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Dlist.Data.Dlist.«term_::_»', expected 'Dlist.Data.Dlist.term_::_._@.Data.Dlist._hyg.47'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- `O(1)` Prepend a single element to a dlist -/
  def
    cons
    ( x : α ) : Dlist α → Dlist α
    | ⟨ xs , h ⟩ => ⟨ x ::_ ∘ xs , by abstract intros ; simp ; rw [ ← h ] ⟩
#align dlist.cons Dlist.cons

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "`O(1)` Append a single element to a dlist -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `concat [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`x] [":" `α] [] ")")]
       [(Term.typeSpec ":" (Term.arrow (Term.app `Dlist [`α]) "→" (Term.app `Dlist [`α])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.anonymousCtor "⟨" [`xs "," `h] "⟩")]]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(«term_∘_» `xs "∘" (Dlist.Data.Dlist.«term_::_» `x "::_"))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.abstract
                  "abstract"
                  []
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.intros "intros" [])
                     ";"
                     (Tactic.simp "simp" [] [] [] [] [])
                     ";"
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `h)
                        ","
                        (Tactic.rwRule [] (Term.app `h [(«term[_]» "[" [`x] "]")]))]
                       "]")
                      [])
                     ";"
                     (Tactic.simp "simp" [] [] [] [] [])])))])))]
            "⟩"))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_∘_» `xs "∘" (Dlist.Data.Dlist.«term_::_» `x "::_"))
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.abstract
             "abstract"
             []
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.intros "intros" [])
                ";"
                (Tactic.simp "simp" [] [] [] [] [])
                ";"
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `h)
                   ","
                   (Tactic.rwRule [] (Term.app `h [(«term[_]» "[" [`x] "]")]))]
                  "]")
                 [])
                ";"
                (Tactic.simp "simp" [] [] [] [] [])])))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.abstract
           "abstract"
           []
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.intros "intros" [])
              ";"
              (Tactic.simp "simp" [] [] [] [] [])
              ";"
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `h)
                 ","
                 (Tactic.rwRule [] (Term.app `h [(«term[_]» "[" [`x] "]")]))]
                "]")
               [])
              ";"
              (Tactic.simp "simp" [] [] [] [] [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.abstract
       "abstract"
       []
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intros "intros" [])
          ";"
          (Tactic.simp "simp" [] [] [] [] [])
          ";"
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] (Term.app `h [(«term[_]» "[" [`x] "]")]))]
            "]")
           [])
          ";"
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] (Term.app `h [(«term[_]» "[" [`x] "]")]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [(«term[_]» "[" [`x] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`x] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `xs "∘" (Dlist.Data.Dlist.«term_::_» `x "::_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Dlist.Data.Dlist.«term_::_» `x "::_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Dlist.Data.Dlist.«term_::_»', expected 'Dlist.Data.Dlist.term_::_._@.Data.Dlist._hyg.47'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- `O(1)` Append a single element to a dlist -/
  def
    concat
    ( x : α ) : Dlist α → Dlist α
    | ⟨ xs , h ⟩ => ⟨ xs ∘ x ::_ , by abstract intros ; simp ; rw [ h , h [ x ] ] ; simp ⟩
#align dlist.concat Dlist.concat

/-- `O(1)` Append dlists -/
protected def append : Dlist α → Dlist α → Dlist α
  | ⟨xs, h₁⟩, ⟨ys, h₂⟩ =>
    ⟨xs ∘ ys, by
      intros
      simp
      rw [h₂, h₁, h₁ (ys List.nil)]
      simp⟩
#align dlist.append Dlist.append

instance : Append (Dlist α) :=
  ⟨Dlist.append⟩

attribute [local simp] of_list to_list Empty singleton cons concat Dlist.append

theorem to_list_of_list (l : List α) : toList (ofList l) = l := by cases l <;> simp
#align dlist.to_list_of_list Dlist.to_list_of_list

theorem of_list_to_list (l : Dlist α) : ofList (toList l) = l :=
  by
  cases' l with xs
  have h : append (xs []) = xs := by
    intros
    funext x
    simp [l_invariant x]
  simp [h]
#align dlist.of_list_to_list Dlist.of_list_to_list

theorem to_list_empty : toList (@empty α) = [] := by simp
#align dlist.to_list_empty Dlist.to_list_empty

theorem to_list_singleton (x : α) : toList (singleton x) = [x] := by simp
#align dlist.to_list_singleton Dlist.to_list_singleton

theorem to_list_append (l₁ l₂ : Dlist α) : toList (l₁ ++ l₂) = toList l₁ ++ toList l₂ :=
  show toList (Dlist.append l₁ l₂) = toList l₁ ++ toList l₂ by
    cases l₁ <;> cases l₂ <;> simp <;> rw [l₁_invariant]
#align dlist.to_list_append Dlist.to_list_append

theorem to_list_cons (x : α) (l : Dlist α) : toList (cons x l) = x :: toList l := by
  cases l <;> simp
#align dlist.to_list_cons Dlist.to_list_cons

theorem to_list_concat (x : α) (l : Dlist α) : toList (concat x l) = toList l ++ [x] := by
  cases l <;> simp <;> rw [l_invariant]
#align dlist.to_list_concat Dlist.to_list_concat

end Dlist

