/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module init.meta.instance_cache
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.Interactive

/-!
# Instance cache tactics

For performance reasons, Lean does not automatically update its database
of class instances during a proof. The group of tactics in this file
helps to force such updates.

-/


open Lean.Parser

open Interactive Interactive.Types

-- mathport name: «expr ?»
local postfix:1024 "?" => optional

-- mathport name: «expr *»
local postfix:1024 "*" => many

namespace Tactic

/-- Reset the instance cache for the main goal. -/
unsafe def reset_instance_cache : tactic Unit := do
  unfreeze_local_instances
  freeze_local_instances
#align tactic.reset_instance_cache tactic.reset_instance_cache

/-- Unfreeze the local instances while executing `tac` on the main goal. -/
unsafe def unfreezing {α} (tac : tactic α) : tactic α :=
  focus1 <| unfreeze_local_instances *> tac <* all_goals freeze_local_instances
#align tactic.unfreezing tactic.unfreezing

/-- Unfreeze local instances while executing `tac`,
if the passed expression is amongst the frozen instances.
-/
unsafe def unfreezing_hyp (h : expr) (tac : tactic Unit) : tactic Unit := do
  let frozen ← frozen_local_instances
  if h ∈ frozen [] then unfreezing tac else tac
#align tactic.unfreezing_hyp tactic.unfreezing_hyp

namespace Interactive

/-- `unfreezingI { tac }` executes tac while temporarily unfreezing the instance cache.
-/
unsafe def unfreezingI (tac : itactic) :=
  unfreezing tac
#align tactic.interactive.unfreezingI tactic.interactive.unfreezingI

/-- Reset the instance cache. This allows any new instances
added to the context to be used in typeclass inference. -/
unsafe def resetI :=
  reset_instance_cache
#align tactic.interactive.resetI tactic.interactive.resetI

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Like `revert`, but can also revert instance arguments. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `revertI [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`ids]
         [":" (Term.app `parse [(Init.Meta.InstanceCache.«term_*» `ident "*")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple ":=" (Term.app `unfreezingI [(Term.app `revert [`ids])]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unfreezingI [(Term.app `revert [`ids])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `revert [`ids])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ids
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `revert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `revert [`ids]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unfreezingI
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [(Init.Meta.InstanceCache.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.InstanceCache.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.«term_*»', expected 'Init.Meta.InstanceCache.term_*._@.Init.Meta.InstanceCache._hyg.54'
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
/-- Like `revert`, but can also revert instance arguments. -/ unsafe
  def revertI ( ids : parse ident * ) : tactic Unit := unfreezingI revert ids
#align tactic.interactive.revertI tactic.interactive.revertI

/-- Like `subst`, but can also substitute in instance arguments. -/
unsafe def substI (q : parse texpr) : tactic Unit :=
  unfreezingI (subst q)
#align tactic.interactive.substI tactic.interactive.substI

/-- Like `cases`, but can also be used with instance arguments. -/
unsafe def casesI (p : parse cases_arg_p) (q : parse with_ident_list) : tactic Unit :=
  unfreezingI (cases p q)
#align tactic.interactive.casesI tactic.interactive.casesI

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Like `intro`, but uses the introduced variable\nin typeclass inference. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `introI [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`p]
         [":" (Term.app `parse [(Init.Meta.InstanceCache.term_? `ident_ "?")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple ":=" («term_>>_» (Term.app `intro [`p]) ">>" `reset_instance_cache) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» (Term.app `intro [`p]) ">>" `reset_instance_cache)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reset_instance_cache
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `intro [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intro
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [(Init.Meta.InstanceCache.term_? `ident_ "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.InstanceCache.term_? `ident_ "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.term_?', expected 'Init.Meta.InstanceCache.term_?._@.Init.Meta.InstanceCache._hyg.9'
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
/--
      Like `intro`, but uses the introduced variable
      in typeclass inference. -/
    unsafe
  def introI ( p : parse ident_ ? ) : tactic Unit := intro p >> reset_instance_cache
#align tactic.interactive.introI tactic.interactive.introI

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Like `intros`, but uses the introduced variable(s)\nin typeclass inference. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `introsI [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`p]
         [":" (Term.app `parse [(Init.Meta.InstanceCache.«term_*» `ident_ "*")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       («term_>>_» (Term.app `intros [`p]) ">>" `reset_instance_cache)
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» (Term.app `intros [`p]) ">>" `reset_instance_cache)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reset_instance_cache
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `intros [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intros
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [(Init.Meta.InstanceCache.«term_*» `ident_ "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.InstanceCache.«term_*» `ident_ "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.«term_*»', expected 'Init.Meta.InstanceCache.term_*._@.Init.Meta.InstanceCache._hyg.54'
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
/--
      Like `intros`, but uses the introduced variable(s)
      in typeclass inference. -/
    unsafe
  def introsI ( p : parse ident_ * ) : tactic Unit := intros p >> reset_instance_cache
#align tactic.interactive.introsI tactic.interactive.introsI

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Used to add typeclasses to the context so that they can\nbe used in typeclass inference. The syntax is the same as `have`. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `haveI [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (Term.app `parse [(Init.Meta.InstanceCache.term_? `ident "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`q₁]
         [":"
          (Term.app
           `parse
           [(Init.Meta.InstanceCache.term_?
             («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `texpr)
             "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`q₂]
         [":"
          (Term.app
           `parse
           [(Init.Meta.InstanceCache.term_?
             («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
             "?")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl
             `h
             []
             "←"
             (Term.doExpr
              (Term.match
               "match"
               []
               []
               [(Term.matchDiscr [] `h)]
               "with"
               (Term.matchAlts
                [(Term.matchAlt "|" [[`none]] "=>" (Term.app `get_unused_name [(str "\"_inst\"")]))
                 (Term.matchAlt "|" [[(Term.app `some [`a])]] "=>" (Term.app `return [`a]))])))))
           [])
          (Term.doSeqItem (Term.doExpr (Term.app `have [(Term.app `some [`h]) `q₁ `q₂])) [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.match
             "match"
             []
             []
             [(Term.matchDiscr [] `q₂)]
             "with"
             (Term.matchAlts
              [(Term.matchAlt
                "|"
                [[`none]]
                "=>"
                («term_>>_» («term_>>_» `swap ">>" `reset_instance_cache) ">>" `swap))
               (Term.matchAlt "|" [[(Term.app `some [`p₂])]] "=>" `reset_instance_cache)])))
           [])]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `h
            []
            "←"
            (Term.doExpr
             (Term.match
              "match"
              []
              []
              [(Term.matchDiscr [] `h)]
              "with"
              (Term.matchAlts
               [(Term.matchAlt "|" [[`none]] "=>" (Term.app `get_unused_name [(str "\"_inst\"")]))
                (Term.matchAlt "|" [[(Term.app `some [`a])]] "=>" (Term.app `return [`a]))])))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `have [(Term.app `some [`h]) `q₁ `q₂])) [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.match
            "match"
            []
            []
            [(Term.matchDiscr [] `q₂)]
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [[`none]]
               "=>"
               («term_>>_» («term_>>_» `swap ">>" `reset_instance_cache) ">>" `swap))
              (Term.matchAlt "|" [[(Term.app `some [`p₂])]] "=>" `reset_instance_cache)])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `q₂)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[`none]]
          "=>"
          («term_>>_» («term_>>_» `swap ">>" `reset_instance_cache) ">>" `swap))
         (Term.matchAlt "|" [[(Term.app `some [`p₂])]] "=>" `reset_instance_cache)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reset_instance_cache
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`p₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_>>_» («term_>>_» `swap ">>" `reset_instance_cache) ">>" `swap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `swap
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      («term_>>_» `swap ">>" `reset_instance_cache)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reset_instance_cache
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      `swap
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1024, (none, [anonymous]) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 60, (some 60, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>_» `swap ">>" `reset_instance_cache)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `have [(Term.app `some [`h]) `q₁ `q₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `some [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `some [`h]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `have
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `h)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt "|" [[`none]] "=>" (Term.app `get_unused_name [(str "\"_inst\"")]))
         (Term.matchAlt "|" [[(Term.app `some [`a])]] "=>" (Term.app `return [`a]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `return [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `get_unused_name [(str "\"_inst\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"_inst\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_unused_name
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `parse
       [(Init.Meta.InstanceCache.term_?
         («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
         "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.InstanceCache.term_? («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.term_?', expected 'Init.Meta.InstanceCache.term_?._@.Init.Meta.InstanceCache._hyg.9'
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
/--
      Used to add typeclasses to the context so that they can
      be used in typeclass inference. The syntax is the same as `have`. -/
    unsafe
  def
    haveI
    ( h : parse ident ? ) ( q₁ : parse tk ":" *> texpr ? ) ( q₂ : parse tk ":=" *> texpr ? )
      : tactic Unit
    :=
      do
        let h ← match h with | none => get_unused_name "_inst" | some a => return a
          have some h q₁ q₂
          match
            q₂
            with
            | none => swap >> reset_instance_cache >> swap | some p₂ => reset_instance_cache
#align tactic.interactive.haveI tactic.interactive.haveI

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Used to add typeclasses to the context so that they can\nbe used in typeclass inference. The syntax is the same as `let`. -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `letI [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (Term.app `parse [(Init.Meta.InstanceCache.term_? `ident "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`q₁]
         [":"
          (Term.app
           `parse
           [(Init.Meta.InstanceCache.term_?
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
           (Init.Meta.InstanceCache.term_?
            («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
            "?"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl
             `h
             []
             "←"
             (Term.doExpr
              (Term.match
               "match"
               []
               []
               [(Term.matchDiscr [] `h)]
               "with"
               (Term.matchAlts
                [(Term.matchAlt "|" [[`none]] "=>" (Term.app `get_unused_name [(str "\"_inst\"")]))
                 (Term.matchAlt "|" [[(Term.app `some [`a])]] "=>" (Term.app `return [`a]))])))))
           [])
          (Term.doSeqItem (Term.doExpr (Term.app `let [(Term.app `some [`h]) `q₁ `q₂])) [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.match
             "match"
             []
             []
             [(Term.matchDiscr [] `q₂)]
             "with"
             (Term.matchAlts
              [(Term.matchAlt
                "|"
                [[`none]]
                "=>"
                («term_>>_» («term_>>_» `swap ">>" `reset_instance_cache) ">>" `swap))
               (Term.matchAlt "|" [[(Term.app `some [`p₂])]] "=>" `reset_instance_cache)])))
           [])]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `h
            []
            "←"
            (Term.doExpr
             (Term.match
              "match"
              []
              []
              [(Term.matchDiscr [] `h)]
              "with"
              (Term.matchAlts
               [(Term.matchAlt "|" [[`none]] "=>" (Term.app `get_unused_name [(str "\"_inst\"")]))
                (Term.matchAlt "|" [[(Term.app `some [`a])]] "=>" (Term.app `return [`a]))])))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `let [(Term.app `some [`h]) `q₁ `q₂])) [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.match
            "match"
            []
            []
            [(Term.matchDiscr [] `q₂)]
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [[`none]]
               "=>"
               («term_>>_» («term_>>_» `swap ">>" `reset_instance_cache) ">>" `swap))
              (Term.matchAlt "|" [[(Term.app `some [`p₂])]] "=>" `reset_instance_cache)])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `q₂)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[`none]]
          "=>"
          («term_>>_» («term_>>_» `swap ">>" `reset_instance_cache) ">>" `swap))
         (Term.matchAlt "|" [[(Term.app `some [`p₂])]] "=>" `reset_instance_cache)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reset_instance_cache
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`p₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_>>_» («term_>>_» `swap ">>" `reset_instance_cache) ">>" `swap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `swap
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      («term_>>_» `swap ">>" `reset_instance_cache)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reset_instance_cache
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      `swap
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1024, (none, [anonymous]) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 60, (some 60, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>_» `swap ">>" `reset_instance_cache)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `let [(Term.app `some [`h]) `q₁ `q₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `q₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `some [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `some [`h]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `let
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `h)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt "|" [[`none]] "=>" (Term.app `get_unused_name [(str "\"_inst\"")]))
         (Term.matchAlt "|" [[(Term.app `some [`a])]] "=>" (Term.app `return [`a]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `return [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `get_unused_name [(str "\"_inst\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"_inst\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_unused_name
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
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
       (Init.Meta.InstanceCache.term_?
        («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
        "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.InstanceCache.term_? («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.InstanceCache.term_?', expected 'Init.Meta.InstanceCache.term_?._@.Init.Meta.InstanceCache._hyg.9'
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
/--
      Used to add typeclasses to the context so that they can
      be used in typeclass inference. The syntax is the same as `let`. -/
    unsafe
  def
    letI
    ( h : parse ident ? ) ( q₁ : parse tk ":" *> texpr ? ) ( q₂ : parse <| tk ":=" *> texpr ? )
      : tactic Unit
    :=
      do
        let h ← match h with | none => get_unused_name "_inst" | some a => return a
          let some h q₁ q₂
          match
            q₂
            with
            | none => swap >> reset_instance_cache >> swap | some p₂ => reset_instance_cache
#align tactic.interactive.letI tactic.interactive.letI

/-- Like `exact`, but uses all variables in the context
for typeclass inference. -/
unsafe def exactI (q : parse texpr) : tactic Unit :=
  reset_instance_cache >> exact q
#align tactic.interactive.exactI tactic.interactive.exactI

end Interactive

end Tactic

