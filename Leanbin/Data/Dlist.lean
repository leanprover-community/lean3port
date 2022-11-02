/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
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

namespace Dlist

open Function

variable {α : Type u}

-- mathport name: «expr♯»
local notation:arg "♯" => by abstract 
  intros
  simp

/-- Convert a list to a dlist -/
def ofList (l : List α) : Dlist α :=
  ⟨append l, ♯⟩

/-- Convert a lazily-evaluated list to a dlist -/
def lazyOfList (l : Thunk' (List α)) : Dlist α :=
  ⟨fun xs => l () ++ xs, ♯⟩

/-- Convert a dlist to a list -/
def toList : Dlist α → List α
  | ⟨xs, _⟩ => xs []

/-- Create a dlist containing no elements -/
def empty : Dlist α :=
  ⟨id, ♯⟩

-- mathport name: «expr ::_»
local notation:arg a "::_" => List.cons a

/-- Create dlist with a single element -/
def singleton (x : α) : Dlist α :=
  ⟨x::_, ♯⟩

attribute [local simp] Function.comp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [(Command.docComment "/--" "`O(1)` Prepend a single element to a dlist -/")] [] [] [] [] [])
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
                     []
                     (Tactic.simp "simp" [] [] [] [] [])
                     []
                     (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]") [])])))])))]
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
                []
                (Tactic.simp "simp" [] [] [] [] [])
                []
                (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]") [])])))])))]
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
              []
              (Tactic.simp "simp" [] [] [] [] [])
              []
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]") [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.abstract
       "abstract"
       []
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intros "intros" [])
          []
          (Tactic.simp "simp" [] [] [] [] [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `h)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
/-- `O(1)` Prepend a single element to a dlist -/
  def cons ( x : α ) : Dlist α → Dlist α | ⟨ xs , h ⟩ => ⟨ x ::_ ∘ xs , by abstract intros simp rw [ ← h ] ⟩

/-- `O(1)` Append a single element to a dlist -/
def concat (x : α) : Dlist α → Dlist α
  | ⟨xs, h⟩ =>
    ⟨xs ∘ x::_, by abstract 
      intros
      simp
      rw [h, h [x]]
      simp⟩

/-- `O(1)` Append dlists -/
protected def append : Dlist α → Dlist α → Dlist α
  | ⟨xs, h₁⟩, ⟨ys, h₂⟩ =>
    ⟨xs ∘ ys, by
      intros
      simp
      rw [h₂, h₁, h₁ (ys List.nil)]
      simp⟩

instance : Append (Dlist α) :=
  ⟨Dlist.append⟩

attribute [local simp] of_list to_list Empty singleton cons concat Dlist.append

theorem to_list_of_list (l : List α) : toList (ofList l) = l := by cases l <;> simp

theorem of_list_to_list (l : Dlist α) : ofList (toList l) = l := by
  cases' l with xs
  have h : append (xs []) = xs := by
    intros
    funext x
    simp [l_invariant x]
  simp [h]

theorem to_list_empty : toList (@empty α) = [] := by simp

theorem to_list_singleton (x : α) : toList (singleton x) = [x] := by simp

theorem to_list_append (l₁ l₂ : Dlist α) : toList (l₁ ++ l₂) = toList l₁ ++ toList l₂ :=
  show toList (Dlist.append l₁ l₂) = toList l₁ ++ toList l₂ by cases l₁ <;> cases l₂ <;> simp <;> rw [l₁_invariant]

theorem to_list_cons (x : α) (l : Dlist α) : toList (cons x l) = x :: toList l := by cases l <;> simp

theorem to_list_concat (x : α) (l : Dlist α) : toList (concat x l) = toList l ++ [x] := by
  cases l <;> simp <;> rw [l_invariant]

end Dlist

