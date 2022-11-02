/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Leanbin.Init.Control.Monad
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Control.State
import Leanbin.Init.Control.Except
import Leanbin.Init.Control.Reader
import Leanbin.Init.Control.Option

universe u v

open Function

open Tactic

unsafe def control_laws_tac :=
  (whnf_target >> intros) >> to_expr (pquote.1 rfl) >>= exact

class IsLawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  map_const_eq : ∀ {α β : Type u}, ((· <$ ·) : α → f β → f α) = (· <$> ·) ∘ const β := by
    intros
    rfl
  -- `functor` is indeed a categorical functor
  id_map : ∀ {α : Type u} (x : f α), id <$> x = x
  comp_map : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x

export IsLawfulFunctor (map_const_eq id_map comp_map)

attribute [simp] id_map

-- `comp_map` does not make a good simp lemma
class LawfulApplicative (f : Type u → Type v) [Applicative f] extends IsLawfulFunctor f : Prop where
  seq_left_eq : ∀ {α β : Type u} (a : f α) (b : f β), a <* b = const β <$> a <*> b := by
    intros
    rfl
  seq_right_eq : ∀ {α β : Type u} (a : f α) (b : f β), a *> b = const α id <$> a <*> b := by
    intros
    rfl
  -- applicative laws
  pure_seq_eq_map : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x
  map_pure : ∀ {α β : Type u} (g : α → β) (x : α), g <$> (pure x : f α) = pure (g x)
  seq_pure : ∀ {α β : Type u} (g : f (α → β)) (x : α), g <*> pure x = (fun g : α → β => g x) <$> g
  seq_assoc :
    ∀ {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)), h <*> (g <*> x) = @comp α β γ <$> h <*> g <*> x
  -- default functor law
  comp_map := by intros <;> simp [(pure_seq_eq_map _ _).symm, seq_assoc, map_pure, seq_pure]

export LawfulApplicative (seq_left_eq seq_right_eq pure_seq_eq_map map_pure seq_pure seq_assoc)

attribute [simp] map_pure seq_pure

/- warning: pure_id_seq -> pure_id_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {f : Type.{u} -> Type.{v}} [_inst_1 : Applicative.{u v} f] [_inst_2 : LawfulApplicative.{u v} f _inst_1] (x : f α), Eq.{succ v} (f α) (Seq.seq.{u v} f (Applicative.toHasSeq.{u v} f _inst_1) α α (Pure.pure.{u v} f (Applicative.toHasPure.{u v} f _inst_1) (α -> α) (id.{succ u} α)) x) x
but is expected to have type
  forall {f : Type.{u_1} -> Type.{u_2}} {α : Type.{u_1}} [inst._@.Init.Control.Lawful._hyg.579 : Applicative.{u_1 u_2} f] [inst._@.Init.Control.Lawful._hyg.582 : LawfulApplicative.{u_1 u_2} f inst._@.Init.Control.Lawful._hyg.579] (x : f α), Eq.{succ u_2} (f α) (Seq.seq.{u_1 u_2} f (Applicative.toSeq.{u_1 u_2} f inst._@.Init.Control.Lawful._hyg.579) α α (Pure.pure.{u_1 u_2} f (Applicative.toPure.{u_1 u_2} f inst._@.Init.Control.Lawful._hyg.579) (α -> α) (id.{succ u_1} α)) (fun (x._@.Init.Control.Lawful._hyg.600 : Unit) => x)) x
Case conversion may be inaccurate. Consider using '#align pure_id_seq pure_id_seqₓ'. -/
-- applicative "law" derivable from other laws
@[simp]
theorem pure_id_seq {α : Type u} {f : Type u → Type v} [Applicative f] [LawfulApplicative f] (x : f α) :
    pure id <*> x = x := by simp [pure_seq_eq_map]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.structure
      (Command.classTk "class")
      (Command.declId `LawfulMonad [])
      [(Term.explicitBinder "(" [`m] [":" (Term.arrow (Term.type "Type" [`u]) "→" (Term.type "Type" [`v]))] [] ")")
       (Term.instBinder "[" [] (Term.app `Monad [`m]) "]")]
      [(Command.extends "extends" [(Term.app `LawfulApplicative [`m])])]
      [(Term.typeSpec ":" (Term.prop "Prop"))]
      ["where"
       []
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `bind_pure_comp_eq_map
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.implicitBinder "{" [`α `β] [":" (Term.type "Type" [`u])] "}")
               (Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" `β)] [] ")")
               (Term.explicitBinder "(" [`x] [":" (Term.app `m [`α])] [] ")")]
              []
              ","
              («term_=_» («term_>>=_» `x ">>=" («term_∘_» `pure "∘" `f)) "=" («term_<$>_» `f "<$>" `x))))])
          [(Term.binderTactic
            ":="
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.intros "intros" []) [] (Tactic.tacticRfl "rfl")])))])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `bind_map_eq_seq
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.implicitBinder "{" [`α `β] [":" (Term.type "Type" [`u])] "}")
               (Term.explicitBinder "(" [`f] [":" (Term.app `m [(Term.arrow `α "→" `β)])] [] ")")
               (Term.explicitBinder "(" [`x] [":" (Term.app `m [`α])] [] ")")]
              []
              ","
              («term_=_»
               («term_>>=_» `f ">>=" (Term.paren "(" [(«term_<$>_» (Term.cdot "·") "<$>" `x) []] ")"))
               "="
               («term_<*>_» `f "<*>" `x))))])
          [(Term.binderTactic
            ":="
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.intros "intros" []) [] (Tactic.tacticRfl "rfl")])))])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `pure_bind
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.implicitBinder "{" [`α `β] [":" (Term.type "Type" [`u])] "}")
               (Term.explicitBinder "(" [`x] [":" `α] [] ")")
               (Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" (Term.app `m [`β]))] [] ")")]
              []
              ","
              («term_=_» («term_>>=_» (Term.app `pure [`x]) ">>=" `f) "=" (Term.app `f [`x]))))])
          [])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `bind_assoc
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.implicitBinder "{" [`α `β `γ] [":" (Term.type "Type" [`u])] "}")
               (Term.explicitBinder "(" [`x] [":" (Term.app `m [`α])] [] ")")
               (Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" (Term.app `m [`β]))] [] ")")
               (Term.explicitBinder "(" [`g] [":" (Term.arrow `β "→" (Term.app `m [`γ]))] [] ")")]
              []
              ","
              («term_=_»
               («term_>>=_» («term_>>=_» `x ">>=" `f) ">>=" `g)
               "="
               («term_>>=_»
                `x
                ">>="
                (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_>>=_» (Term.app `f [`x]) ">>=" `g)))))))])
          [])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `pure_seq_eq_map
          (Command.optDeclSig [] [])
          [(Term.binderDefault
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.intros "intros" [])
                 "<;>"
                 (Tactic.«tactic_<;>_»
                  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `bind_map_eq_seq)] "]") [])
                  "<;>"
                  (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `pure_bind)] "]"] [])))]))))])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `map_pure
          (Command.optDeclSig [] [])
          [(Term.binderDefault
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.intros "intros" [])
                 "<;>"
                 (Tactic.«tactic_<;>_»
                  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `bind_pure_comp_eq_map)] "]") [])
                  "<;>"
                  (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `pure_bind)] "]"] [])))]))))])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `seq_pure
          (Command.optDeclSig [] [])
          [(Term.binderDefault
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.intros "intros" [])
                 "<;>"
                 (Tactic.«tactic_<;>_»
                  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `bind_map_eq_seq)] "]") [])
                  "<;>"
                  (Tactic.simp
                   "simp"
                   []
                   []
                   []
                   ["[" [(Tactic.simpLemma [] [] `map_pure) "," (Tactic.simpLemma [] [] `bind_pure_comp_eq_map)] "]"]
                   [])))]))))])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `seq_assoc
          (Command.optDeclSig [] [])
          [(Term.binderDefault
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.intros "intros" [])
                 "<;>"
                 (Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.proj (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.hole "_")]) "." `symm))
                    ","
                    (Tactic.simpLemma
                     []
                     []
                     (Term.proj (Term.app `bind_map_eq_seq [(Term.hole "_") (Term.hole "_")]) "." `symm))
                    ","
                    (Tactic.simpLemma [] [] `bind_assoc)
                    ","
                    (Tactic.simpLemma [] [] `pure_bind)]
                   "]"]
                  []))]))))])])]
      (Command.optDeriving [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structExplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structInstBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.binderDefault', expected 'Lean.Parser.Term.binderTactic'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.intros "intros" [])
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma
               []
               []
               (Term.proj (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.hole "_")]) "." `symm))
              ","
              (Tactic.simpLemma
               []
               []
               (Term.proj (Term.app `bind_map_eq_seq [(Term.hole "_") (Term.hole "_")]) "." `symm))
              ","
              (Tactic.simpLemma [] [] `bind_assoc)
              ","
              (Tactic.simpLemma [] [] `pure_bind)]
             "]"]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.intros "intros" [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["["
         [(Tactic.simpLemma
           []
           []
           (Term.proj (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.hole "_")]) "." `symm))
          ","
          (Tactic.simpLemma [] [] (Term.proj (Term.app `bind_map_eq_seq [(Term.hole "_") (Term.hole "_")]) "." `symm))
          ","
          (Tactic.simpLemma [] [] `bind_assoc)
          ","
          (Tactic.simpLemma [] [] `pure_bind)]
         "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma
          []
          []
          (Term.proj (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.hole "_")]) "." `symm))
         ","
         (Tactic.simpLemma [] [] (Term.proj (Term.app `bind_map_eq_seq [(Term.hole "_") (Term.hole "_")]) "." `symm))
         ","
         (Tactic.simpLemma [] [] `bind_assoc)
         ","
         (Tactic.simpLemma [] [] `pure_bind)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pure_bind
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bind_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `bind_map_eq_seq [(Term.hole "_") (Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `bind_map_eq_seq [(Term.hole "_") (Term.hole "_")])
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
      `bind_map_eq_seq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     [(Term.app `bind_map_eq_seq [(Term.hole "_") (Term.hole "_")]) []]
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.hole "_")])
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
      `bind_pure_comp_eq_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     [(Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.hole "_")]) []]
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.intros "intros" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structExplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structInstBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.binderDefault', expected 'Lean.Parser.Term.binderTactic'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.intros "intros" [])
           "<;>"
           (Tactic.«tactic_<;>_»
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `bind_map_eq_seq)] "]") [])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `map_pure) "," (Tactic.simpLemma [] [] `bind_pure_comp_eq_map)] "]"]
             [])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.intros "intros" [])
       "<;>"
       (Tactic.«tactic_<;>_»
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `bind_map_eq_seq)] "]") [])
        "<;>"
        (Tactic.simp
         "simp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] `map_pure) "," (Tactic.simpLemma [] [] `bind_pure_comp_eq_map)] "]"]
         [])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `bind_map_eq_seq)] "]") [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["[" [(Tactic.simpLemma [] [] `map_pure) "," (Tactic.simpLemma [] [] `bind_pure_comp_eq_map)] "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `map_pure) "," (Tactic.simpLemma [] [] `bind_pure_comp_eq_map)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bind_pure_comp_eq_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_pure
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `bind_map_eq_seq)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bind_map_eq_seq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'-/-- failed to format: format: uncaught backtrack exception
class
  LawfulMonad
  ( m : Type u → Type v ) [ Monad m ]
  extends LawfulApplicative m
  : Prop
  where
    bind_pure_comp_eq_map : ∀ { α β : Type u } ( f : α → β ) ( x : m α ) , x >>= pure ∘ f = f <$> x := by intros rfl
      bind_map_eq_seq : ∀ { α β : Type u } ( f : m α → β ) ( x : m α ) , f >>= ( · <$> x ) = f <*> x := by intros rfl
      pure_bind : ∀ { α β : Type u } ( x : α ) ( f : α → m β ) , pure x >>= f = f x
      bind_assoc
        : ∀ { α β γ : Type u } ( x : m α ) ( f : α → m β ) ( g : β → m γ ) , x >>= f >>= g = x >>= fun x => f x >>= g
      pure_seq_eq_map := by intros <;> rw [ ← bind_map_eq_seq ] <;> simp [ pure_bind ]
      map_pure := by intros <;> rw [ ← bind_pure_comp_eq_map ] <;> simp [ pure_bind ]
      seq_pure := by intros <;> rw [ ← bind_map_eq_seq ] <;> simp [ map_pure , bind_pure_comp_eq_map ]
      seq_assoc
        := by intros <;> simp [ bind_pure_comp_eq_map _ _ . symm , bind_map_eq_seq _ _ . symm , bind_assoc , pure_bind ]

export LawfulMonad (bind_pure_comp_eq_map bind_map_eq_seq pure_bind bind_assoc)

attribute [simp] pure_bind

/- warning: bind_pure -> bind_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {m : Type.{u} -> Type.{v}} [_inst_1 : Monad.{u v} m] [_inst_2 : LawfulMonad.{u v} m _inst_1] (x : m α), Eq.{succ v} (m α) (Bind.bind.{u v} m (Monad.toHasBind.{u v} m _inst_1) α α x (Pure.pure.{u v} m (Applicative.toHasPure.{u v} m (Monad.toApplicative.{u v} m _inst_1)) α)) x
but is expected to have type
  forall {m : Type.{u_1} -> Type.{u_2}} {α : Type.{u_1}} [inst._@.Init.Control.Lawful._hyg.871 : Monad.{u_1 u_2} m] [inst._@.Init.Control.Lawful._hyg.874 : LawfulMonad.{u_1 u_2} m inst._@.Init.Control.Lawful._hyg.871] (x : m α), Eq.{succ u_2} (m α) (Bind.bind.{u_1 u_2} m (Monad.toBind.{u_1 u_2} m inst._@.Init.Control.Lawful._hyg.871) α α x (Pure.pure.{u_1 u_2} m (Applicative.toPure.{u_1 u_2} m (Monad.toApplicative.{u_1 u_2} m inst._@.Init.Control.Lawful._hyg.871)) α)) x
Case conversion may be inaccurate. Consider using '#align bind_pure bind_pureₓ'. -/
-- monad "law" derivable from other laws
@[simp]
theorem bind_pure {α : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m] (x : m α) : x >>= pure = x :=
  show x >>= pure ∘ id = x by rw [bind_pure_comp_eq_map] <;> simp [id_map]

theorem bind_ext_congr {α β} {m : Type u → Type v} [Bind m] {x : m α} {f g : α → m β} :
    (∀ a, f a = g a) → x >>= f = x >>= g := fun h => by simp [show f = g from funext h]

theorem map_ext_congr {α β} {m : Type u → Type v} [Functor m] {x : m α} {f g : α → β} :
    (∀ a, f a = g a) → (f <$> x : m β) = g <$> x := fun h => by simp [show f = g from funext h]

-- instances of previously defined monads
namespace id

variable {α β : Type}

@[simp]
theorem map_eq (x : id α) (f : α → β) : f <$> x = f x :=
  rfl

@[simp]
theorem bind_eq (x : id α) (f : α → id β) : x >>= f = f x :=
  rfl

@[simp]
theorem pure_eq (a : α) : (pure a : id α) = a :=
  rfl

end id

instance : LawfulMonad id := by refine' { .. } <;> intros <;> rfl

namespace StateT

section

variable {σ : Type u}

variable {m : Type u → Type v}

variable {α β : Type u}

variable (x : StateT σ m α) (st : σ)

theorem ext {x x' : StateT σ m α} (h : ∀ st, x.run st = x'.run st) : x = x' := by
  cases x <;> cases x' <;> simp [show x = x' from funext h]

variable [Monad m]

@[simp]
theorem run_pure (a) : (pure a : StateT σ m α).run st = pure (a, st) :=
  rfl

@[simp]
theorem run_bind (f : α → StateT σ m β) : (x >>= f).run st = x.run st >>= fun p => (f p.1).run p.2 := by
  apply bind_ext_congr <;> intro a <;> cases a <;> simp [StateT.bind, StateT.run]

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
      (Command.declId `run_map [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" `β)] [] ")")
        (Term.instBinder "[" [] (Term.app `LawfulMonad [`m]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj («term_<$>_» `f "<$>" `x) "." `run) [`st])
         "="
         («term_<$>_»
          (Term.fun
           "fun"
           (Term.basicFun
            [`p]
            [(Term.typeSpec ":" («term_×_» `α "×" `σ))]
            "=>"
            (Term.paren
             "("
             [(Term.app `f [(Term.app `Prod.fst [`p])]) [(Term.tupleTail "," [(Term.app `Prod.snd [`p])])]]
             ")")))
          "<$>"
          (Term.app (Term.proj `x "." `run) [`st])))))
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
             [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.app `x.run [`st])]))]
             "]")
            [])
           []
           (Tactic.change
            "change"
            («term_=_»
             (Term.app (Term.proj («term_>>=_» `x ">>=" («term_∘_» `pure "∘" `f)) "." `run) [`st])
             "="
             (Term.hole "_"))
            [])
           []
           (Tactic.simp "simp" [] [] [] [] [])])))
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
            [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.app `x.run [`st])]))]
            "]")
           [])
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.app (Term.proj («term_>>=_» `x ">>=" («term_∘_» `pure "∘" `f)) "." `run) [`st])
            "="
            (Term.hole "_"))
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.app (Term.proj («term_>>=_» `x ">>=" («term_∘_» `pure "∘" `f)) "." `run) [`st])
        "="
        (Term.hole "_"))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (Term.proj («term_>>=_» `x ">>=" («term_∘_» `pure "∘" `f)) "." `run) [`st])
       "="
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj («term_>>=_» `x ">>=" («term_∘_» `pure "∘" `f)) "." `run) [`st])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `st
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_>>=_» `x ">>=" («term_∘_» `pure "∘" `f)) "." `run)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_>>=_» `x ">>=" («term_∘_» `pure "∘" `f))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `pure "∘" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 56 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1024, (none, [anonymous]) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 55, (some 56, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_>>=_» `x ">>=" («term_∘_» `pure "∘" `f)) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.app `x.run [`st])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.app `x.run [`st])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x.run [`st])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `st
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x.run
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `x.run [`st]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bind_pure_comp_eq_map
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
    run_map
    ( f : α → β ) [ LawfulMonad m ] : f <$> x . run st = fun p : α × σ => ( f Prod.fst p , Prod.snd p ) <$> x . run st
    := by rw [ ← bind_pure_comp_eq_map _ x.run st ] change x >>= pure ∘ f . run st = _ simp

@[simp]
theorem run_monad_lift {n} [HasMonadLiftT n m] (x : n α) :
    (monadLift x : StateT σ m α).run st = do
      let a ← (monadLift x : m α)
      pure (a, st) :=
  rfl

@[simp]
theorem run_monad_map {m' n n'} [Monad m'] [MonadFunctorT n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : StateT σ m' α).run st = monadMap (@f) (x.run st) :=
  rfl

@[simp]
theorem run_adapt {σ' σ''} (st : σ) (split : σ → σ' × σ'') (join : σ' → σ'' → σ) (x : StateT σ' m α) :
    (StateT.adapt split join x : StateT σ m α).run st = do
      let (st, ctx) := split st
      let (a, st') ← x.run st
      pure (a, join st' ctx) :=
  by delta StateT.adapt <;> rfl

@[simp]
theorem run_get : (StateT.get : StateT σ m σ).run st = pure (st, st) :=
  rfl

@[simp]
theorem run_put (st') : (StateT.put st' : StateT σ m _).run st = pure (PUnit.unit, st') :=
  rfl

end

end StateT

instance (m : Type u → Type v) [Monad m] [LawfulMonad m] (σ : Type u) : LawfulMonad (StateT σ m) where
  id_map := by intros <;> apply StateT.ext <;> intro <;> simp <;> erw [id_map]
  pure_bind := by
    intros
    apply StateT.ext
    simp
  bind_assoc := by
    intros
    apply StateT.ext
    simp [bind_assoc]

namespace ExceptT

variable {α β ε : Type u} {m : Type u → Type v} (x : ExceptT ε m α)

theorem ext {x x' : ExceptT ε m α} (h : x.run = x'.run) : x = x' := by cases x <;> cases x' <;> simp_all

variable [Monad m]

@[simp]
theorem run_pure (a) : (pure a : ExceptT ε m α).run = pure (@Except.ok ε α a) :=
  rfl

@[simp]
theorem run_bind (f : α → ExceptT ε m β) : (x >>= f).run = x.run >>= ExceptT.bindCont f :=
  rfl

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
      (Command.declId `run_map [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" `β)] [] ")")
        (Term.instBinder "[" [] (Term.app `LawfulMonad [`m]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj («term_<$>_» `f "<$>" `x) "." `run)
         "="
         («term_<$>_» (Term.app `Except.map [`f]) "<$>" (Term.proj `x "." `run)))))
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
             [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") `x.run]))]
             "]")
            [])
           []
           (Tactic.change
            "change"
            («term_=_»
             («term_>>=_» `x.run ">>=" (Term.app `ExceptT.bindCont [(«term_∘_» `pure "∘" `f)]))
             "="
             (Term.hole "_"))
            [])
           []
           (Tactic.apply "apply" `bind_ext_congr)
           []
           (Tactic.«tactic_<;>_»
            (Tactic.intro "intro" [`a])
            "<;>"
            (Tactic.«tactic_<;>_»
             (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
             "<;>"
             (Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] `ExceptT.bindCont) "," (Tactic.simpLemma [] [] `Except.map)] "]"]
              [])))])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") `x.run]))] "]")
           [])
          []
          (Tactic.change
           "change"
           («term_=_»
            («term_>>=_» `x.run ">>=" (Term.app `ExceptT.bindCont [(«term_∘_» `pure "∘" `f)]))
            "="
            (Term.hole "_"))
           [])
          []
          (Tactic.apply "apply" `bind_ext_congr)
          []
          (Tactic.«tactic_<;>_»
           (Tactic.intro "intro" [`a])
           "<;>"
           (Tactic.«tactic_<;>_»
            (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `ExceptT.bindCont) "," (Tactic.simpLemma [] [] `Except.map)] "]"]
             [])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.intro "intro" [`a])
       "<;>"
       (Tactic.«tactic_<;>_»
        (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
        "<;>"
        (Tactic.simp
         "simp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] `ExceptT.bindCont) "," (Tactic.simpLemma [] [] `Except.map)] "]"]
         [])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["[" [(Tactic.simpLemma [] [] `ExceptT.bindCont) "," (Tactic.simpLemma [] [] `Except.map)] "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `ExceptT.bindCont) "," (Tactic.simpLemma [] [] `Except.map)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Except.map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ExceptT.bindCont
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.intro "intro" [`a])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `bind_ext_congr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bind_ext_congr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        («term_>>=_» `x.run ">>=" (Term.app `ExceptT.bindCont [(«term_∘_» `pure "∘" `f)]))
        "="
        (Term.hole "_"))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_>>=_» `x.run ">>=" (Term.app `ExceptT.bindCont [(«term_∘_» `pure "∘" `f)])) "=" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_>>=_» `x.run ">>=" (Term.app `ExceptT.bindCont [(«term_∘_» `pure "∘" `f)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ExceptT.bindCont [(«term_∘_» `pure "∘" `f)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `pure "∘" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_∘_» `pure "∘" `f) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ExceptT.bindCont
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      `x.run
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1024, (none, [anonymous]) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 55, (some 56, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") `x.run]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bind_pure_comp_eq_map [(Term.hole "_") `x.run])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x.run
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bind_pure_comp_eq_map
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
    run_map
    ( f : α → β ) [ LawfulMonad m ] : f <$> x . run = Except.map f <$> x . run
    :=
      by
        rw [ ← bind_pure_comp_eq_map _ x.run ]
          change x.run >>= ExceptT.bindCont pure ∘ f = _
          apply bind_ext_congr
          intro a <;> cases a <;> simp [ ExceptT.bindCont , Except.map ]

@[simp]
theorem run_monad_lift {n} [HasMonadLiftT n m] (x : n α) :
    (monadLift x : ExceptT ε m α).run = Except.ok <$> (monadLift x : m α) :=
  rfl

@[simp]
theorem run_monad_map {m' n n'} [Monad m'] [MonadFunctorT n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : ExceptT ε m' α).run = monadMap (@f) x.run :=
  rfl

end ExceptT

instance (m : Type u → Type v) [Monad m] [LawfulMonad m] (ε : Type u) : LawfulMonad (ExceptT ε m) where
  id_map := by
    intros
    apply ExceptT.ext
    simp only [ExceptT.run_map]
    rw [map_ext_congr, id_map]
    intro a
    cases a <;> rfl
  bind_pure_comp_eq_map := by
    intros
    apply ExceptT.ext
    simp only [ExceptT.run_map, ExceptT.run_bind]
    rw [bind_ext_congr, bind_pure_comp_eq_map]
    intro a
    cases a <;> rfl
  bind_assoc := by
    intros
    apply ExceptT.ext
    simp only [ExceptT.run_bind, bind_assoc]
    rw [bind_ext_congr]
    intro a
    cases a <;> simp [ExceptT.bindCont]
  pure_bind := by intros <;> apply ExceptT.ext <;> simp [ExceptT.bindCont]

namespace ReaderT

section

variable {ρ : Type u}

variable {m : Type u → Type v}

variable {α β : Type u}

variable (x : ReaderT ρ m α) (r : ρ)

theorem ext {x x' : ReaderT ρ m α} (h : ∀ r, x.run r = x'.run r) : x = x' := by
  cases x <;> cases x' <;> simp [show x = x' from funext h]

variable [Monad m]

@[simp]
theorem run_pure (a) : (pure a : ReaderT ρ m α).run r = pure a :=
  rfl

@[simp]
theorem run_bind (f : α → ReaderT ρ m β) : (x >>= f).run r = x.run r >>= fun a => (f a).run r :=
  rfl

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
      (Command.declId `run_map [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" `β)] [] ")")
        (Term.instBinder "[" [] (Term.app `LawfulMonad [`m]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj («term_<$>_» `f "<$>" `x) "." `run) [`r])
         "="
         («term_<$>_» `f "<$>" (Term.app (Term.proj `x "." `run) [`r])))))
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
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.app `x.run [`r])]))]
              "]")
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
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.app `x.run [`r])]))]
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
         [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.app `x.run [`r])]))]
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
        [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.app `x.run [`r])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bind_pure_comp_eq_map [(Term.hole "_") (Term.app `x.run [`r])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x.run [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x.run
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `x.run [`r]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bind_pure_comp_eq_map
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
    run_map
    ( f : α → β ) [ LawfulMonad m ] : f <$> x . run r = f <$> x . run r
    := by rw [ ← bind_pure_comp_eq_map _ x.run r ] <;> rfl

@[simp]
theorem run_monad_lift {n} [HasMonadLiftT n m] (x : n α) : (monadLift x : ReaderT ρ m α).run r = (monadLift x : m α) :=
  rfl

@[simp]
theorem run_monad_map {m' n n'} [Monad m'] [MonadFunctorT n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : ReaderT ρ m' α).run r = monadMap (@f) (x.run r) :=
  rfl

@[simp]
theorem run_read : (ReaderT.read : ReaderT ρ m ρ).run r = pure r :=
  rfl

end

end ReaderT

instance (ρ : Type u) (m : Type u → Type v) [Monad m] [LawfulMonad m] : LawfulMonad (ReaderT ρ m) where
  id_map := by intros <;> apply ReaderT.ext <;> intro <;> simp
  pure_bind := by intros <;> apply ReaderT.ext <;> intro <;> simp
  bind_assoc := by intros <;> apply ReaderT.ext <;> intro <;> simp [bind_assoc]

namespace OptionT

variable {α β : Type u} {m : Type u → Type v} (x : OptionT m α)

theorem ext {x x' : OptionT m α} (h : x.run = x'.run) : x = x' := by cases x <;> cases x' <;> simp_all

variable [Monad m]

@[simp]
theorem run_pure (a) : (pure a : OptionT m α).run = pure (some a) :=
  rfl

@[simp]
theorem run_bind (f : α → OptionT m β) : (x >>= f).run = x.run >>= OptionT.bindCont f :=
  rfl

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
      (Command.declId `run_map [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" `β)] [] ")")
        (Term.instBinder "[" [] (Term.app `LawfulMonad [`m]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj («term_<$>_» `f "<$>" `x) "." `run)
         "="
         («term_<$>_» (Term.app `Option.map [`f]) "<$>" (Term.proj `x "." `run)))))
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
             [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") `x.run]))]
             "]")
            [])
           []
           (Tactic.change
            "change"
            («term_=_»
             («term_>>=_» `x.run ">>=" (Term.app `OptionT.bindCont [(«term_∘_» `pure "∘" `f)]))
             "="
             (Term.hole "_"))
            [])
           []
           (Tactic.apply "apply" `bind_ext_congr)
           []
           (Tactic.«tactic_<;>_»
            (Tactic.intro "intro" [`a])
            "<;>"
            (Tactic.«tactic_<;>_»
             (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
             "<;>"
             (Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `OptionT.bindCont)
                ","
                (Tactic.simpLemma [] [] `Option.map)
                ","
                (Tactic.simpLemma [] [] `Option.bind)]
               "]"]
              [])))])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") `x.run]))] "]")
           [])
          []
          (Tactic.change
           "change"
           («term_=_»
            («term_>>=_» `x.run ">>=" (Term.app `OptionT.bindCont [(«term_∘_» `pure "∘" `f)]))
            "="
            (Term.hole "_"))
           [])
          []
          (Tactic.apply "apply" `bind_ext_congr)
          []
          (Tactic.«tactic_<;>_»
           (Tactic.intro "intro" [`a])
           "<;>"
           (Tactic.«tactic_<;>_»
            (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma [] [] `OptionT.bindCont)
               ","
               (Tactic.simpLemma [] [] `Option.map)
               ","
               (Tactic.simpLemma [] [] `Option.bind)]
              "]"]
             [])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.intro "intro" [`a])
       "<;>"
       (Tactic.«tactic_<;>_»
        (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
        "<;>"
        (Tactic.simp
         "simp"
         []
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `OptionT.bindCont)
           ","
           (Tactic.simpLemma [] [] `Option.map)
           ","
           (Tactic.simpLemma [] [] `Option.bind)]
          "]"]
         [])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `OptionT.bindCont)
          ","
          (Tactic.simpLemma [] [] `Option.map)
          ","
          (Tactic.simpLemma [] [] `Option.bind)]
         "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `OptionT.bindCont)
         ","
         (Tactic.simpLemma [] [] `Option.map)
         ","
         (Tactic.simpLemma [] [] `Option.bind)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Option.bind
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Option.map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `OptionT.bindCont
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `a)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.intro "intro" [`a])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `bind_ext_congr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bind_ext_congr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        («term_>>=_» `x.run ">>=" (Term.app `OptionT.bindCont [(«term_∘_» `pure "∘" `f)]))
        "="
        (Term.hole "_"))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_>>=_» `x.run ">>=" (Term.app `OptionT.bindCont [(«term_∘_» `pure "∘" `f)])) "=" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_>>=_» `x.run ">>=" (Term.app `OptionT.bindCont [(«term_∘_» `pure "∘" `f)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `OptionT.bindCont [(«term_∘_» `pure "∘" `f)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `pure "∘" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_∘_» `pure "∘" `f) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `OptionT.bindCont
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      `x.run
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1024, (none, [anonymous]) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 55, (some 56, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `bind_pure_comp_eq_map [(Term.hole "_") `x.run]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bind_pure_comp_eq_map [(Term.hole "_") `x.run])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x.run
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bind_pure_comp_eq_map
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
    run_map
    ( f : α → β ) [ LawfulMonad m ] : f <$> x . run = Option.map f <$> x . run
    :=
      by
        rw [ ← bind_pure_comp_eq_map _ x.run ]
          change x.run >>= OptionT.bindCont pure ∘ f = _
          apply bind_ext_congr
          intro a <;> cases a <;> simp [ OptionT.bindCont , Option.map , Option.bind ]

@[simp]
theorem run_monad_lift {n} [HasMonadLiftT n m] (x : n α) :
    (monadLift x : OptionT m α).run = some <$> (monadLift x : m α) :=
  rfl

@[simp]
theorem run_monad_map {m' n n'} [Monad m'] [MonadFunctorT n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : OptionT m' α).run = monadMap (@f) x.run :=
  rfl

end OptionT

instance (m : Type u → Type v) [Monad m] [LawfulMonad m] : LawfulMonad (OptionT m) where
  id_map := by
    intros
    apply OptionT.ext
    simp only [OptionT.run_map]
    rw [map_ext_congr, id_map]
    intro a
    cases a <;> rfl
  bind_assoc := by
    intros
    apply OptionT.ext
    simp only [OptionT.run_bind, bind_assoc]
    rw [bind_ext_congr]
    intro a
    cases a <;> simp [OptionT.bindCont]
  pure_bind := by intros <;> apply OptionT.ext <;> simp [OptionT.bindCont]

