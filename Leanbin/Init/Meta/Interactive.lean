/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg

! This file was ported from Lean 3 source module init.meta.interactive
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.TypeContext
import Leanbin.Init.Meta.RewriteTactic
import Leanbin.Init.Meta.SimpTactic
import Leanbin.Init.Meta.Smt.CongruenceClosure
import Leanbin.Init.Control.Combinators
import Leanbin.Init.Meta.InteractiveBase
import Leanbin.Init.Meta.Derive
import Leanbin.Init.Meta.MatchTactic
import Leanbin.Init.Meta.CongrTactic
import Leanbin.Init.Meta.CaseTag

open Lean

open Lean.Parser

open Native

/- ./././Mathport/Syntax/Translate/Command.lean:671:29: warning: unsupported: precedence command -/
-- mathport name: «expr ?»
local postfix:1024 "?" => optional

-- mathport name: «expr *»
local postfix:1024 "*" => many

namespace Tactic

/-- allows metavars -/
unsafe def i_to_expr (q : pexpr) : tactic expr :=
  to_expr q true
#align tactic.i_to_expr tactic.i_to_expr

/-- allow metavars and no subgoals -/
unsafe def i_to_expr_no_subgoals (q : pexpr) : tactic expr :=
  to_expr q true false
#align tactic.i_to_expr_no_subgoals tactic.i_to_expr_no_subgoals

/-- doesn't allows metavars -/
unsafe def i_to_expr_strict (q : pexpr) : tactic expr :=
  to_expr q false
#align tactic.i_to_expr_strict tactic.i_to_expr_strict

/-- Auxiliary version of i_to_expr for apply-like tactics.
   This is a workaround for comment
      https://github.com/leanprover/lean/issues/1342#issuecomment-307912291
   at issue #1342.

   In interactive mode, given a tactic

        apply f

   we want the apply tactic to create all metavariables. The following
   definition will return `@f` for `f`. That is, it will **not** create
   metavariables for implicit arguments.

   Before we added `i_to_expr_for_apply`, the tactic

       apply le_antisymm

   would first elaborate `le_antisymm`, and create

       @le_antisymm ?m_1 ?m_2 ?m_3 ?m_4

   The type class resolution problem
        ?m_2 : weak_order ?m_1
   by the elaborator since ?m_1 is not assigned yet, and the problem is
   discarded.

   Then, we would invoke `apply_core`, which would create two
   new metavariables for the explicit arguments, and try to unify the resulting
   type with the current target. After the unification,
   the metavariables ?m_1, ?m_3 and ?m_4 are assigned, but we lost
   the information about the pending type class resolution problem.

   With `i_to_expr_for_apply`, `le_antisymm` is elaborate into `@le_antisymm`,
   the apply_core tactic creates all metavariables, and solves the ones that
   can be solved by type class resolution.

   Another possible fix: we modify the elaborator to return pending
   type class resolution problems, and store them in the tactic_state.
-/
unsafe def i_to_expr_for_apply (q : pexpr) : tactic expr :=
  let aux (n : Name) : tactic expr := do
    let p ← resolve_name n
    match p with
      | expr.const c [] => do
        let r ← mk_const c
        save_type_info r q
        return r
      | _ => i_to_expr p
  match q with
  | expr.const c [] => aux c
  | expr.local_const c _ _ _ => aux c
  | _ => i_to_expr q
#align tactic.i_to_expr_for_apply tactic.i_to_expr_for_apply

namespace Interactive

open _Root_.Interactive Interactive.Types Expr

/-- itactic: parse a nested "interactive" tactic. That is, parse
  `{` tactic `}`
-/
unsafe def itactic : Type :=
  tactic Unit
#align tactic.interactive.itactic tactic.interactive.itactic

unsafe def propagate_tags (tac : itactic) : tactic Unit := do
  let tag ← get_main_tag
  if tag = [] then tac
    else
      focus1 do
        tac
        let gs ← get_goals
        (when (not gs)) do
            let new_tag ← get_main_tag
            when new_tag <| with_enable_tags (set_main_tag tag)
#align tactic.interactive.propagate_tags tactic.interactive.propagate_tags

unsafe def concat_tags (tac : tactic (List (Name × expr))) : tactic Unit :=
  condM tags_enabled
    (do
      let in_tag ← get_main_tag
      let r ← tac
      let r
        ←-- remove assigned metavars
              r.mfilter
            fun ⟨n, m⟩ => not <$> is_assigned m
      match r with
        | [(_, m)] => set_tag m in_tag
        |-- if there is only new subgoal, we just propagate `in_tag`
          _ =>
          r fun ⟨n, m⟩ => set_tag m (n :: in_tag))
    (tac >> skip)
#align tactic.interactive.concat_tags tactic.interactive.concat_tags

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If the current goal is a Pi/forall `∀ x : t, u` (resp. `let x := t in u`) then `intro` puts `x : t` (resp. `x := t`) in the local context. The new subgoal target is `u`.\n\nIf the goal is an arrow `t → u`, then it puts `h : t` in the local context and the new goal target is `u`.\n\nIf the goal is neither a Pi/forall nor begins with a let binder, the tactic `intro` applies the tactic `whnf` until an introduction can be applied or the goal is not head reducible. In the latter case, the tactic fails.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `intro [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app `parse [(Init.Meta.Interactive.term_? `ident_ "?")])
          "→"
          (Term.app `tactic [`Unit])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`none]]
           "=>"
           (Term.app `propagate_tags [(«term_>>_» `intro1 ">>" `skip)]))
          (Term.matchAlt
           "|"
           [[(Term.app `some [`h])]]
           "=>"
           (Term.app `propagate_tags [(«term_>>_» (Term.app `tactic.intro [`h]) ">>" `skip)]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `propagate_tags [(«term_>>_» (Term.app `tactic.intro [`h]) ">>" `skip)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» (Term.app `tactic.intro [`h]) ">>" `skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `tactic.intro [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.intro
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>_» (Term.app `tactic.intro [`h]) ">>" `skip)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `propagate_tags
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `propagate_tags [(«term_>>_» `intro1 ">>" `skip)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» `intro1 ">>" `skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      `intro1
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1024, (none, [anonymous]) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_>>_» `intro1 ">>" `skip) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `propagate_tags
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app `parse [(Init.Meta.Interactive.term_? `ident_ "?")])
       "→"
       (Term.app `tactic [`Unit]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `parse [(Init.Meta.Interactive.term_? `ident_ "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? `ident_ "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      If the current goal is a Pi/forall `∀ x : t, u` (resp. `let x := t in u`) then `intro` puts `x : t` (resp. `x := t`) in the local context. The new subgoal target is `u`.
      
      If the goal is an arrow `t → u`, then it puts `h : t` in the local context and the new goal target is `u`.
      
      If the goal is neither a Pi/forall nor begins with a let binder, the tactic `intro` applies the tactic `whnf` until an introduction can be applied or the goal is not head reducible. In the latter case, the tactic fails.
      -/
    unsafe
  def
    intro
    : parse ident_ ? → tactic Unit
    | none => propagate_tags intro1 >> skip | some h => propagate_tags tactic.intro h >> skip
#align tactic.interactive.intro tactic.interactive.intro

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Similar to `intro` tactic. The tactic `intros` will keep introducing new hypotheses until the goal target is not a Pi/forall or let binder.\n\nThe variant `intros h₁ ... hₙ` introduces `n` new hypotheses using the given identifiers to name them.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `intros [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident_ "*")])
          "→"
          (Term.app `tactic [`Unit])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]")]]
           "=>"
           (Term.app `propagate_tags [(«term_>>_» `tactic.intros ">>" `skip)]))
          (Term.matchAlt
           "|"
           [[`hs]]
           "=>"
           (Term.app `propagate_tags [(«term_>>_» (Term.app `intro_lst [`hs]) ">>" `skip)]))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `propagate_tags [(«term_>>_» (Term.app `intro_lst [`hs]) ">>" `skip)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» (Term.app `intro_lst [`hs]) ">>" `skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `intro_lst [`hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intro_lst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>_» (Term.app `intro_lst [`hs]) ">>" `skip)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `propagate_tags
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `propagate_tags [(«term_>>_» `tactic.intros ">>" `skip)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» `tactic.intros ">>" `skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      `tactic.intros
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1024, (none, [anonymous]) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>_» `tactic.intros ">>" `skip)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `propagate_tags
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident_ "*")])
       "→"
       (Term.app `tactic [`Unit]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident_ "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident_ "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Similar to `intro` tactic. The tactic `intros` will keep introducing new hypotheses until the goal target is not a Pi/forall or let binder.
      
      The variant `intros h₁ ... hₙ` introduces `n` new hypotheses using the given identifiers to name them.
      -/
    unsafe
  def
    intros
    : parse ident_ * → tactic Unit
    | [ ] => propagate_tags tactic.intros >> skip | hs => propagate_tags intro_lst hs >> skip
#align tactic.interactive.intros tactic.interactive.intros

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The tactic `introv` allows the user to automatically introduce the variables of a theorem and explicitly name the hypotheses involved. The given names are used to name non-dependent hypotheses.\n\nExamples:\n```\nexample : ∀ a b : nat, a = b → b = a :=\nbegin\n  introv h,\n  exact h.symm\nend\n```\nThe state after `introv h` is\n```\na b : ℕ,\nh : a = b\n⊢ b = a\n```\n\n```\nexample : ∀ a b : nat, a = b → ∀ c, b = c → a = c :=\nbegin\n  introv h₁ h₂,\n  exact h₁.trans h₂\nend\n```\nThe state after `introv h₁ h₂` is\n```\na b : ℕ,\nh₁ : a = b,\nc : ℕ,\nh₂ : b = c\n⊢ a = c\n```\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `introv [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`ns]
         [":" (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident_ "*")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.app
        `propagate_tags
        [(«term_>>_»
          (Term.app `tactic.introv [`ns])
          ">>"
          (Term.app `return [(Term.tuple "(" [] ")")]))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `propagate_tags
       [(«term_>>_»
         (Term.app `tactic.introv [`ns])
         ">>"
         (Term.app `return [(Term.tuple "(" [] ")")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» (Term.app `tactic.introv [`ns]) ">>" (Term.app `return [(Term.tuple "(" [] ")")]))
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
      (Term.app `tactic.introv [`ns])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ns
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.introv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>_» (Term.app `tactic.introv [`ns]) ">>" (Term.app `return [(Term.tuple "(" [] ")")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `propagate_tags
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
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident_ "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident_ "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
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
      The tactic `introv` allows the user to automatically introduce the variables of a theorem and explicitly name the hypotheses involved. The given names are used to name non-dependent hypotheses.
      
      Examples:
      ```
      example : ∀ a b : nat, a = b → b = a :=
      begin
        introv h,
        exact h.symm
      end
      ```
      The state after `introv h` is
      ```
      a b : ℕ,
      h : a = b
      ⊢ b = a
      ```
      
      ```
      example : ∀ a b : nat, a = b → ∀ c, b = c → a = c :=
      begin
        introv h₁ h₂,
        exact h₁.trans h₂
      end
      ```
      The state after `introv h₁ h₂` is
      ```
      a b : ℕ,
      h₁ : a = b,
      c : ℕ,
      h₂ : b = c
      ⊢ a = c
      ```
      -/
    unsafe
  def introv ( ns : parse ident_ * ) : tactic Unit := propagate_tags tactic.introv ns >> return ( )
#align tactic.interactive.introv tactic.interactive.introv

/-- Parse a current name and new name for `rename`. -/
private unsafe def rename_arg_parser : parser (Name × Name) :=
  Prod.mk <$> ident <*> (optional (tk "->") *> ident)
#align tactic.interactive.rename_arg_parser tactic.interactive.rename_arg_parser

/-- Parse the arguments of `rename`. -/
private unsafe def rename_args_parser : parser (List (Name × Name)) :=
  Functor.map (fun x => [x]) rename_arg_parser <|>
    tk "[" *> sep_by (tk ",") rename_arg_parser <* tk "]"
#align tactic.interactive.rename_args_parser tactic.interactive.rename_args_parser

/-- Rename one or more local hypotheses. The renamings are given as follows:

```
rename x y             -- rename x to y
rename x → y           -- ditto
rename [x y, a b]      -- rename x to y and a to b
rename [x → y, a → b]  -- ditto
```

Note that if there are multiple hypotheses called `x` in the context, then
`rename x y` will rename *all* of them. If you want to rename only one, use
`dedup` first.
-/
unsafe def rename (renames : parse rename_args_parser) : tactic Unit :=
  propagate_tags <| tactic.rename_many <| native.rb_map.of_list renames
#align tactic.interactive.rename tactic.interactive.rename

/--
The `apply` tactic tries to match the current goal against the conclusion of the type of term. The argument term should be a term well-formed in the local context of the main goal. If it succeeds, then the tactic returns as many subgoals as the number of premises that have not been fixed by type inference or type class resolution. Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution, and first-order unification with dependent types.
-/
unsafe def apply (q : parse texpr) : tactic Unit :=
  concat_tags do
    let h ← i_to_expr_for_apply q
    tactic.apply h
#align tactic.interactive.apply tactic.interactive.apply

/-- Similar to the `apply` tactic, but does not reorder goals.
-/
unsafe def fapply (q : parse texpr) : tactic Unit :=
  concat_tags (i_to_expr_for_apply q >>= tactic.fapply)
#align tactic.interactive.fapply tactic.interactive.fapply

/--
Similar to the `apply` tactic, but only creates subgoals for non-dependent premises that have not been fixed by type inference or type class resolution.
-/
unsafe def eapply (q : parse texpr) : tactic Unit :=
  concat_tags (i_to_expr_for_apply q >>= tactic.eapply)
#align tactic.interactive.eapply tactic.interactive.eapply

/--
Similar to the `apply` tactic, but allows the user to provide a `apply_cfg` configuration object.
-/
unsafe def apply_with (q : parse parser.pexpr) (cfg : ApplyCfg) : tactic Unit :=
  concat_tags do
    let e ← i_to_expr_for_apply q
    tactic.apply e cfg
#align tactic.interactive.apply_with tactic.interactive.apply_with

/-- Similar to the `apply` tactic, but uses matching instead of unification.
`apply_match t` is equivalent to `apply_with t {unify := ff}`
-/
unsafe def mapply (q : parse texpr) : tactic Unit :=
  concat_tags do
    let e ← i_to_expr_for_apply q
    tactic.apply e { unify := ff }
#align tactic.interactive.mapply tactic.interactive.mapply

/--
This tactic tries to close the main goal `... ⊢ t` by generating a term of type `t` using type class resolution.
-/
unsafe def apply_instance : tactic Unit :=
  tactic.apply_instance
#align tactic.interactive.apply_instance tactic.interactive.apply_instance

/--
This tactic behaves like `exact`, but with a big difference: the user can put underscores `_` in the expression as placeholders for holes that need to be filled, and `refine` will generate as many subgoals as there are holes.

Note that some holes may be implicit. The type of each hole must either be synthesized by the system or declared by an explicit type ascription like `(_ : nat → Prop)`.
-/
unsafe def refine (q : parse texpr) : tactic Unit :=
  tactic.refine q
#align tactic.interactive.refine tactic.interactive.refine

/--
This tactic looks in the local context for a hypothesis whose type is equal to the goal target. If it finds one, it uses it to prove the goal, and otherwise it fails.
-/
unsafe def assumption : tactic Unit :=
  tactic.assumption
#align tactic.interactive.assumption tactic.interactive.assumption

/-- Try to apply `assumption` to all goals. -/
unsafe def assumption' : tactic Unit :=
  tactic.any_goals' tactic.assumption
#align tactic.interactive.assumption' tactic.interactive.assumption'

private unsafe def change_core (e : expr) : Option expr → tactic Unit
  | none => tactic.change e
  | some h => do
    let num_reverted : ℕ ← revert h
    let expr.pi n bi d b ← target
    tactic.change <| expr.pi n bi e b
    intron num_reverted
#align tactic.interactive.change_core tactic.interactive.change_core

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`change u` replaces the target `t` of the main goal to `u` provided that `t` is well formed with respect to the local context of the main goal and `t` and `u` are definitionally equal.\n\n`change u at h` will change a local hypothesis to `u`.\n\n`change t with u at h1 h2 ...` will replace `t` with `u` in all the supplied hypotheses (or `*`), or in the goal if no `at` clause is specified, provided that `t` and `u` are definitionally equal.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `change [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`q] [":" (Term.app `parse [`texpr])] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app
           `parse
           [(Init.Meta.Interactive.term_?
             («term_*>_» (Term.app `tk [(str "\"with\"")]) "*>" `texpr)
             "?")])
          "→"
          (Term.arrow (Term.app `parse [`location]) "→" (Term.app `tactic [`Unit]))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`none "," (Term.app `loc.ns [(«term[_]» "[" [`none] "]")])]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`q]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `change_core [`e `none])) [])])))
          (Term.matchAlt
           "|"
           [[`none "," (Term.app `loc.ns [(«term[_]» "[" [(Term.app `some [`h])] "]")])]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `eq [] "←" (Term.doExpr (Term.app `i_to_expr [`q]))))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `eh [] "←" (Term.doExpr (Term.app `get_local [`h]))))
               [])
              (Term.doSeqItem
               (Term.doExpr (Term.app `change_core [`Eq (Term.app `some [`eh])]))
               [])])))
          (Term.matchAlt
           "|"
           [[`none "," (Term.hole "_")]]
           "=>"
           (Term.app `fail [(str "\"change-at does not support multiple locations\"")]))
          (Term.matchAlt
           "|"
           [[(Term.app `some [`w]) "," `l]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl
                 `ty
                 []
                 "←"
                 (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl
                 `eq
                 []
                 "←"
                 (Term.doExpr
                  (Term.app
                   `i_to_expr
                   [(Term.precheckedQuot
                     "`"
                     (Term.quot
                      "`("
                      (Term.typeAscription
                       "("
                       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `q ")") [])
                       ":"
                       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                       ")")
                      ")"))]))))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl
                 `ew
                 []
                 "←"
                 (Term.doExpr
                  (Term.app
                   `i_to_expr
                   [(Term.precheckedQuot
                     "`"
                     (Term.quot
                      "`("
                      (Term.typeAscription
                       "("
                       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `w ")") [])
                       ":"
                       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                       ")")
                      ")"))]))))
               [])
              (Term.doSeqItem
               (Term.doLet
                "let"
                []
                (Term.letDecl
                 (Term.letIdDecl
                  `repl
                  []
                  []
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`e]
                    [(Term.typeSpec ":" `expr)]
                    "=>"
                    (Term.app
                     (Term.proj `e "." `replace)
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`a `n]
                        []
                        "=>"
                        (termIfThenElse
                         "if"
                         («term_=_» `a "=" `Eq)
                         "then"
                         (Term.app `some [`ew])
                         "else"
                         `none)))]))))))
               [])
              (Term.doSeqItem
               (Term.doExpr
                (Term.app
                 `l
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`h]
                    []
                    "=>"
                    (Term.do
                     "do"
                     (Term.doSeqIndent
                      [(Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `infer_type [`h]))))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr
                         (Term.app `change_core [(Term.app `repl [`e]) (Term.app `some [`h])]))
                        [])]))))
                  (Term.do
                   "do"
                   (Term.doSeqIndent
                    [(Term.doSeqItem
                      (Term.doLetArrow "let" [] (Term.doIdDecl `g [] "←" (Term.doExpr `target)))
                      [])
                     (Term.doSeqItem
                      (Term.doExpr (Term.app `change_core [(Term.app `repl [`g]) `none]))
                      [])]))]))
               [])])))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `ty [] "←" (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `eq
            []
            "←"
            (Term.doExpr
             (Term.app
              `i_to_expr
              [(Term.precheckedQuot
                "`"
                (Term.quot
                 "`("
                 (Term.typeAscription
                  "("
                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `q ")") [])
                  ":"
                  [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                  ")")
                 ")"))]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `ew
            []
            "←"
            (Term.doExpr
             (Term.app
              `i_to_expr
              [(Term.precheckedQuot
                "`"
                (Term.quot
                 "`("
                 (Term.typeAscription
                  "("
                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `w ")") [])
                  ":"
                  [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
                  ")")
                 ")"))]))))
          [])
         (Term.doSeqItem
          (Term.doLet
           "let"
           []
           (Term.letDecl
            (Term.letIdDecl
             `repl
             []
             []
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`e]
               [(Term.typeSpec ":" `expr)]
               "=>"
               (Term.app
                (Term.proj `e "." `replace)
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`a `n]
                   []
                   "=>"
                   (termIfThenElse
                    "if"
                    («term_=_» `a "=" `Eq)
                    "then"
                    (Term.app `some [`ew])
                    "else"
                    `none)))]))))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `l
            [(Term.fun
              "fun"
              (Term.basicFun
               [`h]
               []
               "=>"
               (Term.do
                "do"
                (Term.doSeqIndent
                 [(Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `infer_type [`h]))))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr
                    (Term.app `change_core [(Term.app `repl [`e]) (Term.app `some [`h])]))
                   [])]))))
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow "let" [] (Term.doIdDecl `g [] "←" (Term.doExpr `target)))
                 [])
                (Term.doSeqItem
                 (Term.doExpr (Term.app `change_core [(Term.app `repl [`g]) `none]))
                 [])]))]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `l
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `infer_type [`h]))))
              [])
             (Term.doSeqItem
              (Term.doExpr (Term.app `change_core [(Term.app `repl [`e]) (Term.app `some [`h])]))
              [])]))))
        (Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow "let" [] (Term.doIdDecl `g [] "←" (Term.doExpr `target)))
            [])
           (Term.doSeqItem
            (Term.doExpr (Term.app `change_core [(Term.app `repl [`g]) `none]))
            [])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `g [] "←" (Term.doExpr `target)))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `change_core [(Term.app `repl [`g]) `none])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `change_core [(Term.app `repl [`g]) `none])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `repl [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `repl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `repl [`g]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `change_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `target
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `infer_type [`h]))))
            [])
           (Term.doSeqItem
            (Term.doExpr (Term.app `change_core [(Term.app `repl [`e]) (Term.app `some [`h])]))
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `infer_type [`h]))))
          [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `change_core [(Term.app `repl [`e]) (Term.app `some [`h])]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `change_core [(Term.app `repl [`e]) (Term.app `some [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `some [`h]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `repl [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `repl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `repl [`e]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `change_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `infer_type [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `infer_type
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`h]
       []
       "=>"
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `infer_type [`h]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `change_core
             [(Term.paren "(" (Term.app `repl [`e]) ")")
              (Term.paren "(" (Term.app `some [`h]) ")")]))
           [])]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.fun
       "fun"
       (Term.basicFun
        [`e]
        [(Term.typeSpec ":" `expr)]
        "=>"
        (Term.app
         (Term.proj `e "." `replace)
         [(Term.fun
           "fun"
           (Term.basicFun
            [`a `n]
            []
            "=>"
            (termIfThenElse
             "if"
             («term_=_» `a "=" `Eq)
             "then"
             (Term.app `some [`ew])
             "else"
             `none)))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `e "." `replace)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a `n]
          []
          "=>"
          (termIfThenElse
           "if"
           («term_=_» `a "=" `Eq)
           "then"
           (Term.app `some [`ew])
           "else"
           `none)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `n]
        []
        "=>"
        (termIfThenElse "if" («term_=_» `a "=" `Eq) "then" (Term.app `some [`ew]) "else" `none)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse "if" («term_=_» `a "=" `Eq) "then" (Term.app `some [`ew]) "else" `none)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`ew])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ew
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `a "=" `Eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Eq
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `e "." `replace)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `expr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `i_to_expr
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.typeAscription
           "("
           (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `w ")") [])
           ":"
           [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
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
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `w ")") [])
         ":"
         [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
         ")")
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `w ")") [])
       ":"
       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `w ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `i_to_expr
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.typeAscription
           "("
           (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `q ")") [])
           ":"
           [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
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
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `q ")") [])
         ":"
         [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
         ")")
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `q ")") [])
       ":"
       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])]
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `ty ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `q ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `mk_meta_var [(Term.app `sort [`u])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sort [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sort
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `sort [`u]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk_meta_var
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `mk_meta_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`w])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `fail [(str "\"change-at does not support multiple locations\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"change-at does not support multiple locations\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fail
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
           (Term.doIdDecl `eq [] "←" (Term.doExpr (Term.app `i_to_expr [`q]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `eh [] "←" (Term.doExpr (Term.app `get_local [`h]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `change_core [`Eq (Term.app `some [`eh])])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `change_core [`Eq (Term.app `some [`eh])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`eh])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eh
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `some [`eh]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Eq
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `change_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `get_local [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_local
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `i_to_expr [`q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `loc.ns [(«term[_]» "[" [(Term.app `some [`h])] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [(Term.app `some [`h])] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `loc.ns
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
           (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`q]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `change_core [`e `none])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `change_core [`e `none])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `change_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `i_to_expr [`q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `loc.ns [(«term[_]» "[" [`none] "]")])
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
      `loc.ns
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app
        `parse
        [(Init.Meta.Interactive.term_?
          («term_*>_» (Term.app `tk [(str "\"with\"")]) "*>" `texpr)
          "?")])
       "→"
       (Term.arrow (Term.app `parse [`location]) "→" (Term.app `tactic [`Unit])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `parse [`location]) "→" (Term.app `tactic [`Unit]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `parse [`location])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `location
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `parse
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app
       `parse
       [(Init.Meta.Interactive.term_?
         («term_*>_» (Term.app `tk [(str "\"with\"")]) "*>" `texpr)
         "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? («term_*>_» (Term.app `tk [(str "\"with\"")]) "*>" `texpr) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `change u` replaces the target `t` of the main goal to `u` provided that `t` is well formed with respect to the local context of the main goal and `t` and `u` are definitionally equal.
      
      `change u at h` will change a local hypothesis to `u`.
      
      `change t with u at h1 h2 ...` will replace `t` with `u` in all the supplied hypotheses (or `*`), or in the goal if no `at` clause is specified, provided that `t` and `u` are definitionally equal.
      -/
    unsafe
  def
    change
    ( q : parse texpr ) : parse tk "with" *> texpr ? → parse location → tactic Unit
    | none , loc.ns [ none ] => do let e ← i_to_expr q change_core e none
      |
        none , loc.ns [ some h ]
        =>
        do let eq ← i_to_expr q let eh ← get_local h change_core Eq some eh
      | none , _ => fail "change-at does not support multiple locations"
      |
        some w , l
        =>
        do
          let u ← mk_meta_univ
            let ty ← mk_meta_var sort u
            let eq ← i_to_expr ` `( ( $ ( q ) : $ ( ty ) ) )
            let ew ← i_to_expr ` `( ( $ ( w ) : $ ( ty ) ) )
            let repl := fun e : expr => e . replace fun a n => if a = Eq then some ew else none
            l
              fun h => do let e ← infer_type h change_core repl e some h
                do let g ← target change_core repl g none
#align tactic.interactive.change tactic.interactive.change

/--
This tactic provides an exact proof term to solve the main goal. If `t` is the goal and `p` is a term of type `u` then `exact p` succeeds if and only if `t` and `u` can be unified.
-/
unsafe def exact (q : parse texpr) : tactic Unit := do
  let tgt : expr ← target
  i_to_expr_strict ``(($(q) : $(tgt))) >>= tactic.exact
#align tactic.interactive.exact tactic.interactive.exact

/--
Like `exact`, but takes a list of terms and checks that all goals are discharged after the tactic.
-/
unsafe def exacts : parse pexpr_list_or_texpr → tactic Unit
  | [] => done
  | t :: ts => exact t >> exacts ts
#align tactic.interactive.exacts tactic.interactive.exacts

/-- A synonym for `exact` that allows writing `have/suffices/show ..., from ...` in tactic mode.
-/
unsafe def from :=
  exact
#align tactic.interactive.from tactic.interactive.from

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`revert h₁ ... hₙ` applies to any goal with hypotheses `h₁` ... `hₙ`. It moves the hypotheses and their dependencies to the target of the goal. This tactic is the inverse of `intro`.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `revert [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`ids]
         [":" (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.app
        `propagate_tags
        [(Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl `hs [] "←" (Term.doExpr (Term.app `mapM [`tactic.get_local `ids]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `revert_lst [`hs])) [])
            (Term.doSeqItem (Term.doExpr `skip) [])]))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `propagate_tags
       [(Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl `hs [] "←" (Term.doExpr (Term.app `mapM [`tactic.get_local `ids]))))
            [])
           (Term.doSeqItem (Term.doExpr (Term.app `revert_lst [`hs])) [])
           (Term.doSeqItem (Term.doExpr `skip) [])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `hs [] "←" (Term.doExpr (Term.app `mapM [`tactic.get_local `ids]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `revert_lst [`hs])) [])
         (Term.doSeqItem (Term.doExpr `skip) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `revert_lst [`hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `revert_lst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `mapM [`tactic.get_local `ids])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ids
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `tactic.get_local
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mapM
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `propagate_tags
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
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
      `revert h₁ ... hₙ` applies to any goal with hypotheses `h₁` ... `hₙ`. It moves the hypotheses and their dependencies to the target of the goal. This tactic is the inverse of `intro`.
      -/
    unsafe
  def
    revert
    ( ids : parse ident * ) : tactic Unit
    := propagate_tags do let hs ← mapM tactic.get_local ids revert_lst hs skip
#align tactic.interactive.revert tactic.interactive.revert

private unsafe def resolve_name' (n : Name) : tactic expr := do
  let p ← resolve_name n
  match p with
    | expr.const n _ => mk_const n
    |-- create metavars for universe levels
      _ =>
      i_to_expr p
#align tactic.interactive.resolve_name' tactic.interactive.resolve_name'

/--
Version of to_expr that tries to bypass the elaborator if `p` is just a constant or local constant.
   This is not an optimization, by skipping the elaborator we make sure that no unwanted resolution is used.
   Example: the elaborator will force any unassigned ?A that must have be an instance of (has_one ?A) to nat.
   Remark: another benefit is that auxiliary temporary metavariables do not appear in error messages. -/
unsafe def to_expr' (p : pexpr) : tactic expr :=
  match p with
  | const c [] => do
    let new_e ← resolve_name' c
    save_type_info new_e p
    return new_e
  | local_const c _ _ _ => do
    let new_e ← resolve_name' c
    save_type_info new_e p
    return new_e
  | _ => i_to_expr p
#align tactic.interactive.to_expr' tactic.interactive.to_expr'

unsafe structure rw_rule where
  Pos : Pos
  symm : Bool
  rule : pexpr
  deriving has_reflect
#align tactic.interactive.rw_rule tactic.interactive.rw_rule

unsafe def get_rule_eqn_lemmas (r : rw_rule) : tactic (List Name) :=
  let aux (n : Name) : tactic (List Name) :=
    (-- unpack local refs
      do
        let p ← resolve_name n
        let e := p.erase_annotations.get_app_fn.erase_annotations
        match e with
          | const n _ => get_eqn_lemmas_for tt n
          | _ => return []) <|>
      return []
  match r.rule with
  | const n _ => aux n
  | local_const n _ _ _ => aux n
  | _ => return []
#align tactic.interactive.get_rule_eqn_lemmas tactic.interactive.get_rule_eqn_lemmas

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `eq_lemmas -/
private unsafe def rw_goal (cfg : RewriteCfg) (rs : List rw_rule) : tactic Unit :=
  rs.mmap' fun r => do
    save_info r
    let eq_lemmas ← get_rule_eqn_lemmas r
    orelse'
        (do
          let e ← to_expr' r
          rewrite_target e { cfg with symm := r })
        (eq_lemmas fun n => do
          let e ← mk_const n
          rewrite_target e { cfg with symm := r })
        (eq_lemmas eq_lemmas.empty)
#align tactic.interactive.rw_goal tactic.interactive.rw_goal

private unsafe def uses_hyp (e : expr) (h : expr) : Bool :=
  (e.fold false) fun t _ r => r || decide (t = h)
#align tactic.interactive.uses_hyp tactic.interactive.uses_hyp

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `eq_lemmas -/
private unsafe def rw_hyp (cfg : RewriteCfg) : List rw_rule → expr → tactic Unit
  | [], hyp => skip
  | r :: rs, hyp => do
    save_info r
    let eq_lemmas ← get_rule_eqn_lemmas r
    orelse'
        (do
          let e ← to_expr' r
          (if uses_hyp e hyp then pure e else rewrite_hyp e hyp { cfg with symm := r }) >>=
              rw_hyp rs)
        (eq_lemmas fun n => do
          let e ← mk_const n
          rewrite_hyp e hyp { cfg with symm := r } >>= rw_hyp rs)
        (eq_lemmas eq_lemmas.empty)
#align tactic.interactive.rw_hyp tactic.interactive.rw_hyp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [(Command.unsafe "unsafe")] [])
     (Command.def
      "def"
      (Command.declId `rw_rule_p [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`ep] [":" (Term.app `parser [`pexpr])] [] ")")]
       [(Term.typeSpec ":" (Term.app `parser [`rw_rule]))])
      (Command.declValSimple
       ":="
       («term_<*>_»
        («term_<*>_»
         («term_<$>_» `rw_rule.mk "<$>" `cur_pos)
         "<*>"
         («term_<$>_»
          `Option.isSome
          "<$>"
          (Init.Meta.Interactive.term_?
           (Term.app
            `with_desc
            [(str "\"←\"")
             («term_<|>_» (Term.app `tk [(str "\"←\"")]) "<|>" (Term.app `tk [(str "\"<-\"")]))])
           "?")))
        "<*>"
        `ep)
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<*>_»
       («term_<*>_»
        («term_<$>_» `rw_rule.mk "<$>" `cur_pos)
        "<*>"
        («term_<$>_»
         `Option.isSome
         "<$>"
         (Init.Meta.Interactive.term_?
          (Term.app
           `with_desc
           [(str "\"←\"")
            («term_<|>_» (Term.app `tk [(str "\"←\"")]) "<|>" (Term.app `tk [(str "\"<-\"")]))])
          "?")))
       "<*>"
       `ep)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ep
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      («term_<*>_»
       («term_<$>_» `rw_rule.mk "<$>" `cur_pos)
       "<*>"
       («term_<$>_»
        `Option.isSome
        "<$>"
        (Init.Meta.Interactive.term_?
         (Term.app
          `with_desc
          [(str "\"←\"")
           («term_<|>_» (Term.app `tk [(str "\"←\"")]) "<|>" (Term.app `tk [(str "\"<-\"")]))])
         "?")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<$>_»
       `Option.isSome
       "<$>"
       (Init.Meta.Interactive.term_?
        (Term.app
         `with_desc
         [(str "\"←\"")
          («term_<|>_» (Term.app `tk [(str "\"←\"")]) "<|>" (Term.app `tk [(str "\"<-\"")]))])
        "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_?
       (Term.app
        `with_desc
        [(str "\"←\"")
         («term_<|>_» (Term.app `tk [(str "\"←\"")]) "<|>" (Term.app `tk [(str "\"<-\"")]))])
       "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
unsafe
  def
    rw_rule_p
    ( ep : parser pexpr ) : parser rw_rule
    := rw_rule.mk <$> cur_pos <*> Option.isSome <$> with_desc "←" tk "←" <|> tk "<-" ? <*> ep
#align tactic.interactive.rw_rule_p tactic.interactive.rw_rule_p

unsafe structure rw_rules_t where
  rules : List rw_rule
  end_pos : Option Pos
  deriving has_reflect
#align tactic.interactive.rw_rules_t tactic.interactive.rw_rules_t

-- accepts the same content as `pexpr_list_or_texpr`, but with correct goal info pos annotations
unsafe def rw_rules : parser rw_rules_t :=
  tk "[" *>
        rw_rules_t.mk <$>
          sep_by (skip_info (tk ",")) (set_goal_info_pos <| rw_rule_p (parser.pexpr 0)) <*>
      (some <$> cur_pos <* set_goal_info_pos (tk "]")) <|>
    rw_rules_t.mk <$> List.ret <$> rw_rule_p texpr <*> return none
#align tactic.interactive.rw_rules tactic.interactive.rw_rules

private unsafe def rw_core (rs : parse rw_rules) (loca : parse location) (cfg : RewriteCfg) :
    tactic Unit :=
  ((match loca with
      | loc.wildcard => loca.try_apply (rw_hyp cfg rs.rules) (rw_goal cfg rs.rules)
      | _ => loca.apply (rw_hyp cfg rs.rules) (rw_goal cfg rs.rules)) >>
      try (reflexivity reducible)) >>
    (returnopt rs.end_pos >>= save_info <|> skip)
#align tactic.interactive.rw_core tactic.interactive.rw_core

/--
`rewrite e` applies identity `e` as a rewrite rule to the target of the main goal. If `e` is preceded by left arrow (`←` or `<-`), the rewrite is applied in the reverse direction. If `e` is a defined constant, then the equational lemmas associated with `e` are used. This provides a convenient way to unfold `e`.

`rewrite [e₁, ..., eₙ]` applies the given rules sequentially.

`rewrite e at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a list of hypotheses in the local context. In the latter case, a turnstile `⊢` or `|-` can also be used, to signify the target of the goal.
-/
unsafe def rewrite (q : parse rw_rules) (l : parse location) (cfg : RewriteCfg := { }) :
    tactic Unit :=
  propagate_tags (rw_core q l cfg)
#align tactic.interactive.rewrite tactic.interactive.rewrite

/-- An abbreviation for `rewrite`.
-/
unsafe def rw (q : parse rw_rules) (l : parse location) (cfg : RewriteCfg := { }) : tactic Unit :=
  propagate_tags (rw_core q l cfg)
#align tactic.interactive.rw tactic.interactive.rw

/-- `rewrite` followed by `assumption`.
-/
unsafe def rwa (q : parse rw_rules) (l : parse location) (cfg : RewriteCfg := { }) : tactic Unit :=
  rewrite q l cfg >> try assumption
#align tactic.interactive.rwa tactic.interactive.rwa

/--
A variant of `rewrite` that uses the unifier more aggressively, unfolding semireducible definitions.
-/
unsafe def erewrite (q : parse rw_rules) (l : parse location)
    (cfg : RewriteCfg := { md := semireducible }) : tactic Unit :=
  propagate_tags (rw_core q l cfg)
#align tactic.interactive.erewrite tactic.interactive.erewrite

/-- An abbreviation for `erewrite`.
-/
unsafe def erw (q : parse rw_rules) (l : parse location)
    (cfg : RewriteCfg := { md := semireducible }) : tactic Unit :=
  propagate_tags (rw_core q l cfg)
#align tactic.interactive.erw tactic.interactive.erw

/-- Returns the unique names of all hypotheses (local constants) in the context.
-/
private unsafe def hyp_unique_names : tactic name_set := do
  let ctx ← local_context
  pure <| ctx (fun r h => r h) mk_name_set
#align tactic.interactive.hyp_unique_names tactic.interactive.hyp_unique_names

/-- Returns all hypotheses (local constants) from the context except those whose
unique names are in `hyp_uids`.
-/
private unsafe def hyps_except (hyp_uids : name_set) : tactic (List expr) := do
  let ctx ← local_context
  pure <| ctx fun h : expr => ¬hyp_uids h
#align tactic.interactive.hyps_except tactic.interactive.hyps_except

/-- Apply `t` to the main goal and revert any new hypothesis in the generated goals.
If `t` is a supported tactic or chain of supported tactics (e.g. `induction`,
`cases`, `apply`, `constructor`), the generated goals are also tagged with case
tags. You can then use `case` to focus such tagged goals.

Two typical uses of `with_cases`:

1. Applying a custom eliminator:

   ```
   lemma my_nat_rec :
     ∀ n {P : ℕ → Prop} (zero : P 0) (succ : ∀ n, P n → P (n + 1)), P n := ...

   example (n : ℕ) : n = n :=
   begin
     with_cases { apply my_nat_rec n },
     case zero { refl },
     case succ : m ih { refl }
   end
   ```

2. Enabling the use of `case` after a chain of case-splitting tactics:

   ```
   example (n m : ℕ) : unit :=
   begin
     with_cases { cases n; induction m },
     case nat.zero nat.zero { exact () },
     case nat.zero nat.succ : k { exact () },
     case nat.succ nat.zero : i { exact () },
     case nat.succ nat.succ : k i ih_i { exact () }
   end
   ```
-/
unsafe def with_cases (t : itactic) : tactic Unit :=
  with_enable_tags <|
    focus1 do
      let input_hyp_uids ← hyp_unique_names
      t
      all_goals' do
          let in_tag ← get_main_tag
          let new_hyps ← hyps_except input_hyp_uids
          let n ← revert_lst new_hyps
          set_main_tag (case_tag.from_tag_pi in_tag n).render
#align tactic.interactive.with_cases tactic.interactive.with_cases

private unsafe def generalize_arg_p_aux : pexpr → parser (pexpr × Name)
  | app (app (macro _ [const `eq _]) h) (local_const x _ _ _) => pure (h, x)
  | _ => fail "parse error"
#align tactic.interactive.generalize_arg_p_aux tactic.interactive.generalize_arg_p_aux

private unsafe def generalize_arg_p : parser (pexpr × Name) :=
  with_desc "expr = id" <| parser.pexpr 0 >>= generalize_arg_p_aux
#align tactic.interactive.generalize_arg_p tactic.interactive.generalize_arg_p

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`generalize : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of the same type.\n\n`generalize h : e = x` in addition registers the hypothesis `h : e = x`.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `generalize [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [(Term.hole "_")]
         [":" («term_<|_» `parse "<|" (Term.app `tk [(str "\":\"")]))]
         []
         ")")
        (Term.explicitBinder "(" [`p] [":" (Term.app `parse [`generalize_arg_p])] [] ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.app
        `propagate_tags
        [(Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLet
              "let"
              []
              (Term.letDecl (Term.letPatDecl (Term.tuple "(" [`p "," [`x]] ")") [] [] ":=" `p)))
             [])
            (Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
             [])
            (Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doPatDecl
               (Term.app `some [`h])
               "←"
               (Term.doExpr (Term.app `pure [`h]))
               ["|"
                (Term.doSeqIndent
                 [(Term.doSeqItem
                   (Term.doExpr
                    («term_>>_»
                     («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `intro1)
                     ">>"
                     `skip))
                   [])])]))
             [])
            (Term.doSeqItem
             (Term.doLetArrow "let" [] (Term.doIdDecl `tgt [] "←" (Term.doExpr `target)))
             [])
            (Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl
               `tgt'
               []
               "←"
               (Term.doExpr
                («term_<|>_»
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doPatDecl
                       (Term.anonymousCtor "⟨" [`tgt' "," (Term.hole "_")] "⟩")
                       "←"
                       (Term.doExpr
                        (Term.app
                         `solve_aux
                         [`tgt («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `target)]))
                       []))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr
                      (Term.app
                       `to_expr
                       [(Term.precheckedQuot
                         "`"
                         (Term.quot
                          "`("
                          (Term.forall
                           "∀"
                           [`x]
                           []
                           ","
                           (Term.arrow
                            («term_=_»
                             (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                             "="
                             `x)
                            "→"
                            (term.pseudo.antiquot
                             "$"
                             []
                             (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
                             [])))
                          ")"))]))
                     [])]))
                 "<|>"
                 (Term.app
                  `to_expr
                  [(Term.precheckedQuot
                    "`"
                    (Term.quot
                     "`("
                     (Term.forall
                      "∀"
                      [`x]
                      []
                      ","
                      (Term.arrow
                       («term_=_»
                        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                        "="
                        `x)
                       "→"
                       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `tgt ")") [])))
                     ")"))])))))
             [])
            (Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `assert [`h `tgt']))))
             [])
            (Term.doSeqItem (Term.doExpr `swap) [])
            (Term.doSeqItem
             (Term.doExpr
              (Term.app
               `exact
               [(Term.precheckedQuot
                 "`"
                 (Term.quot
                  "`("
                  (Term.app
                   (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])
                   [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) `rfl])
                  ")"))]))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `intro [`x])) [])
            (Term.doSeqItem (Term.doExpr (Term.app `intro [`h])) [])]))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `propagate_tags
       [(Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLet
             "let"
             []
             (Term.letDecl (Term.letPatDecl (Term.tuple "(" [`p "," [`x]] ")") [] [] ":=" `p)))
            [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
            [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doPatDecl
              (Term.app `some [`h])
              "←"
              (Term.doExpr (Term.app `pure [`h]))
              ["|"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doExpr
                   («term_>>_»
                    («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `intro1)
                    ">>"
                    `skip))
                  [])])]))
            [])
           (Term.doSeqItem
            (Term.doLetArrow "let" [] (Term.doIdDecl `tgt [] "←" (Term.doExpr `target)))
            [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl
              `tgt'
              []
              "←"
              (Term.doExpr
               («term_<|>_»
                (Term.do
                 "do"
                 (Term.doSeqIndent
                  [(Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doPatDecl
                      (Term.anonymousCtor "⟨" [`tgt' "," (Term.hole "_")] "⟩")
                      "←"
                      (Term.doExpr
                       (Term.app
                        `solve_aux
                        [`tgt («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `target)]))
                      []))
                    [])
                   (Term.doSeqItem
                    (Term.doExpr
                     (Term.app
                      `to_expr
                      [(Term.precheckedQuot
                        "`"
                        (Term.quot
                         "`("
                         (Term.forall
                          "∀"
                          [`x]
                          []
                          ","
                          (Term.arrow
                           («term_=_»
                            (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                            "="
                            `x)
                           "→"
                           (term.pseudo.antiquot
                            "$"
                            []
                            (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
                            [])))
                         ")"))]))
                    [])]))
                "<|>"
                (Term.app
                 `to_expr
                 [(Term.precheckedQuot
                   "`"
                   (Term.quot
                    "`("
                    (Term.forall
                     "∀"
                     [`x]
                     []
                     ","
                     (Term.arrow
                      («term_=_»
                       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                       "="
                       `x)
                      "→"
                      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `tgt ")") [])))
                    ")"))])))))
            [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `assert [`h `tgt']))))
            [])
           (Term.doSeqItem (Term.doExpr `swap) [])
           (Term.doSeqItem
            (Term.doExpr
             (Term.app
              `exact
              [(Term.precheckedQuot
                "`"
                (Term.quot
                 "`("
                 (Term.app
                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])
                  [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) `rfl])
                 ")"))]))
            [])
           (Term.doSeqItem (Term.doExpr (Term.app `intro [`x])) [])
           (Term.doSeqItem (Term.doExpr (Term.app `intro [`h])) [])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLet
           "let"
           []
           (Term.letDecl (Term.letPatDecl (Term.tuple "(" [`p "," [`x]] ")") [] [] ":=" `p)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.app `some [`h])
            "←"
            (Term.doExpr (Term.app `pure [`h]))
            ["|"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doExpr
                 («term_>>_»
                  («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `intro1)
                  ">>"
                  `skip))
                [])])]))
          [])
         (Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `tgt [] "←" (Term.doExpr `target)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `tgt'
            []
            "←"
            (Term.doExpr
             («term_<|>_»
              (Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doPatDecl
                    (Term.anonymousCtor "⟨" [`tgt' "," (Term.hole "_")] "⟩")
                    "←"
                    (Term.doExpr
                     (Term.app
                      `solve_aux
                      [`tgt («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `target)]))
                    []))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr
                   (Term.app
                    `to_expr
                    [(Term.precheckedQuot
                      "`"
                      (Term.quot
                       "`("
                       (Term.forall
                        "∀"
                        [`x]
                        []
                        ","
                        (Term.arrow
                         («term_=_»
                          (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                          "="
                          `x)
                         "→"
                         (term.pseudo.antiquot
                          "$"
                          []
                          (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
                          [])))
                       ")"))]))
                  [])]))
              "<|>"
              (Term.app
               `to_expr
               [(Term.precheckedQuot
                 "`"
                 (Term.quot
                  "`("
                  (Term.forall
                   "∀"
                   [`x]
                   []
                   ","
                   (Term.arrow
                    («term_=_»
                     (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                     "="
                     `x)
                    "→"
                    (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `tgt ")") [])))
                  ")"))])))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `assert [`h `tgt']))))
          [])
         (Term.doSeqItem (Term.doExpr `swap) [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `exact
            [(Term.precheckedQuot
              "`"
              (Term.quot
               "`("
               (Term.app
                (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])
                [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) `rfl])
               ")"))]))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `intro [`x])) [])
         (Term.doSeqItem (Term.doExpr (Term.app `intro [`h])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `intro [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intro
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `intro [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intro
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app
       `exact
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.app
           (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])
           [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) `rfl])
          ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.precheckedQuot
       "`"
       (Term.quot
        "`("
        (Term.app
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])
         [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) `rfl])
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])
       [(term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `t ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exact
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      `swap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `assert [`h `tgt'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tgt'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `assert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      («term_<|>_»
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doPatDecl
             (Term.anonymousCtor "⟨" [`tgt' "," (Term.hole "_")] "⟩")
             "←"
             (Term.doExpr
              (Term.app
               `solve_aux
               [`tgt («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `target)]))
             []))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `to_expr
             [(Term.precheckedQuot
               "`"
               (Term.quot
                "`("
                (Term.forall
                 "∀"
                 [`x]
                 []
                 ","
                 (Term.arrow
                  («term_=_»
                   (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                   "="
                   `x)
                  "→"
                  (term.pseudo.antiquot
                   "$"
                   []
                   (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
                   [])))
                ")"))]))
           [])]))
       "<|>"
       (Term.app
        `to_expr
        [(Term.precheckedQuot
          "`"
          (Term.quot
           "`("
           (Term.forall
            "∀"
            [`x]
            []
            ","
            (Term.arrow
             («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
             "→"
             (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `tgt ")") [])))
           ")"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `to_expr
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.forall
           "∀"
           [`x]
           []
           ","
           (Term.arrow
            («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
            "→"
            (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `tgt ")") [])))
          ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.precheckedQuot
       "`"
       (Term.quot
        "`("
        (Term.forall
         "∀"
         [`x]
         []
         ","
         (Term.arrow
          («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
          "→"
          (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `tgt ")") [])))
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       []
       ","
       (Term.arrow
        («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
        "→"
        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `tgt ")") [])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
       "→"
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `tgt ")") []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `tgt ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.anonymousCtor "⟨" [`tgt' "," (Term.hole "_")] "⟩")
            "←"
            (Term.doExpr
             (Term.app
              `solve_aux
              [`tgt («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `target)]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `to_expr
            [(Term.precheckedQuot
              "`"
              (Term.quot
               "`("
               (Term.forall
                "∀"
                [`x]
                []
                ","
                (Term.arrow
                 («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
                 "→"
                 (term.pseudo.antiquot
                  "$"
                  []
                  (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
                  [])))
               ")"))]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `to_expr
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.forall
           "∀"
           [`x]
           []
           ","
           (Term.arrow
            («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
            "→"
            (term.pseudo.antiquot
             "$"
             []
             (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
             [])))
          ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.precheckedQuot', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.precheckedQuot
       "`"
       (Term.quot
        "`("
        (Term.forall
         "∀"
         [`x]
         []
         ","
         (Term.arrow
          («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
          "→"
          (term.pseudo.antiquot
           "$"
           []
           (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
           [])))
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       []
       ","
       (Term.arrow
        («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
        "→"
        (term.pseudo.antiquot
         "$"
         []
         (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
         [])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
       "→"
       (term.pseudo.antiquot
        "$"
        []
        (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot
       "$"
       []
       (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `solve_aux [`tgt («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `target)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_>>_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `target)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `target
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `tactic.generalize [`e `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.generalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `target)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `tgt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `solve_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`tgt' "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tgt'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1023, (some 0, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.do
      "do"
      (Term.doSeqIndent
       [(Term.doSeqItem
         (Term.doLetArrow
          "let"
          []
          (Term.doPatDecl
           (Term.anonymousCtor "⟨" [`tgt' "," (Term.hole "_")] "⟩")
           "←"
           (Term.doExpr
            (Term.app
             `solve_aux
             [`tgt
              (Term.paren
               "("
               («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `target)
               ")")]))
           []))
         [])
        (Term.doSeqItem
         (Term.doExpr
          (Term.app
           `to_expr
           [(Term.precheckedQuot
             "`"
             (Term.quot
              "`("
              (Term.forall
               "∀"
               [`x]
               []
               ","
               (Term.arrow
                («term_=_» (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []) "=" `x)
                "→"
                (term.pseudo.antiquot
                 "$"
                 []
                 (antiquotNestedExpr "(" (Term.app `tgt' [(num "0") (num "1")]) ")")
                 [])))
              ")"))]))
         [])]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 20, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `target
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      («term_>>_» («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `intro1) ">>" `skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `intro1)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `intro1
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `tactic.generalize [`e `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.generalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 60, (some 60, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_>>_» (Term.app `tactic.generalize [`e `x]) ">>" `intro1)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `i_to_expr [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`p "," [`x]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `propagate_tags
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
      (Term.app `parse [`generalize_arg_p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `generalize_arg_p
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
      («term_<|_» `parse "<|" (Term.app `tk [(str "\":\"")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tk [(str "\":\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\":\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `parse
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? `ident "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `generalize : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of the same type.
      
      `generalize h : e = x` in addition registers the hypothesis `h : e = x`.
      -/
    unsafe
  def
    generalize
    ( h : parse ident ? ) ( _ : parse <| tk ":" ) ( p : parse generalize_arg_p ) : tactic Unit
    :=
      propagate_tags
        do
          let ( p , x ) := p
            let e ← i_to_expr p
            let some h ← pure h | tactic.generalize e x >> intro1 >> skip
            let tgt ← target
            let
              tgt'
                ←
                do
                    let ⟨ tgt' , _ ⟩ ← solve_aux tgt tactic.generalize e x >> target
                      to_expr ` `( ∀ x , $ ( e ) = x → $ ( tgt' 0 1 ) )
                  <|>
                  to_expr ` `( ∀ x , $ ( e ) = x → $ ( tgt ) )
            let t ← assert h tgt'
            swap
            exact ` `( $ ( t ) $ ( e ) rfl )
            intro x
            intro h
#align tactic.interactive.generalize tactic.interactive.generalize

unsafe def cases_arg_p : parser (Option Name × pexpr) :=
  (with_desc "(id :)? expr") do
    let t ← texpr
    match t with
      | local_const x _ _ _ =>
        (tk ":" *> do
            let t ← texpr
            pure (some x, t)) <|>
          pure (none, t)
      | _ => pure (none, t)
#align tactic.interactive.cases_arg_p tactic.interactive.cases_arg_p

/-- Updates the tags of new subgoals produced by `cases` or `induction`. `in_tag`
  is the initial tag, i.e. the tag of the goal on which `cases`/`induction` was
  applied. `rs` should contain, for each subgoal, the constructor name
  associated with that goal and the hypotheses that were introduced.
-/
private unsafe def set_cases_tags (in_tag : Tag) (rs : List (Name × List expr)) : tactic Unit := do
  let gs ← get_goals
  match gs with
    |-- if only one goal was produced, we should not make the tag longer
      [g] =>
      set_tag g in_tag
    | _ =>
      let tgs : List (Name × List expr × expr) := rs (fun ⟨n, new_hyps⟩ g => ⟨n, new_hyps, g⟩) gs
      tgs fun ⟨n, new_hyps, g⟩ =>
        with_enable_tags <|
          set_tag g <| (case_tag.from_tag_hyps (n :: in_tag) (new_hyps expr.local_uniq_name)).render
#align tactic.interactive.set_cases_tags tactic.interactive.set_cases_tags

/- ./././Mathport/Syntax/Translate/Command.lean:671:29: warning: unsupported: precedence command -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Assuming `x` is a variable in the local context with an inductive type, `induction x` applies induction on `x` to the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor and an inductive hypothesis is added for each recursive argument to the constructor. If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward, so that the inductive hypothesis incorporates that hypothesis as well.\n\nFor example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `induction n` produces one goal with hypothesis `h : P 0` and target `Q 0`, and one goal with hypotheses `h : P (nat.succ a)` and `ih₁ : P a → Q a` and target `Q (nat.succ a)`. Here the names `a` and `ih₁` ire chosen automatically.\n\n`induction e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then performs induction on the resulting variable.\n\n`induction e with y₁ ... yₙ`, where `e` is a variable or an expression, specifies that the sequence of names `y₁ ... yₙ` should be used for the arguments to the constructors and inductive hypotheses, including implicit arguments. If the list does not include enough names for all of the arguments, additional names are generated automatically. If too many names are given, the extra ones are ignored. Underscores can be used in the list, in which case the corresponding names are generated automatically. Note that for long sequences of names, the `case` tactic provides a more convenient naming mechanism.\n\n`induction e using r` allows the user to specify the principle of induction that should be used. Here `r` should be a theorem whose result type must be of the form `C t`, where `C` is a bound variable and `t` is a (possibly empty) sequence of bound variables\n\n`induction e generalizing z₁ ... zₙ`, where `z₁ ... zₙ` are variables in the local context, generalizes over `z₁ ... zₙ` before applying the induction but then introduces them in each goal. In other words, the net effect is that each inductive hypothesis is generalized.\n\n`induction h : t` will introduce an equality of the form `h : t = C x y`, asserting that the input term is equal to the current constructor case, to the context.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `induction [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`hp] [":" (Term.app `parse [`cases_arg_p])] [] ")")
        (Term.explicitBinder "(" [`rec_name] [":" (Term.app `parse [`using_ident])] [] ")")
        (Term.explicitBinder "(" [`ids] [":" (Term.app `parse [`with_ident_list])] [] ")")
        (Term.explicitBinder
         "("
         [`revert]
         [":"
          («term_<|_»
           `parse
           "<|"
           (Init.Meta.Interactive.term_?
            («term_*>_»
             (Term.app `tk [(str "\"generalizing\"")])
             "*>"
             (Init.Meta.Interactive.«term_*» `ident "*"))
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
           (Term.doLetArrow "let" [] (Term.doIdDecl `in_tag [] "←" (Term.doExpr `get_main_tag)))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `focus1
             [(Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl
                    `e
                    []
                    "←"
                    (Term.doExpr
                     (Term.match
                      "match"
                      []
                      []
                      [(Term.matchDiscr [] `hp)]
                      "with"
                      (Term.matchAlts
                       [(Term.matchAlt
                         "|"
                         [[(Term.tuple "(" [(Term.app `some [`h]) "," [`p]] ")")]]
                         "=>"
                         (Term.do
                          "do"
                          (Term.doSeqIndent
                           [(Term.doSeqItem
                             (Term.doLetArrow
                              "let"
                              []
                              (Term.doIdDecl `x [] "←" (Term.doExpr `get_unused_name)))
                             [])
                            (Term.doSeqItem
                             (Term.doExpr
                              (Term.app
                               `generalize
                               [`h (Term.tuple "(" [] ")") (Term.tuple "(" [`p "," [`x]] ")")]))
                             [])
                            (Term.doSeqItem (Term.doExpr (Term.app `get_local [`x])) [])])))
                        (Term.matchAlt
                         "|"
                         [[(Term.tuple "(" [`none "," [`p]] ")")]]
                         "=>"
                         (Term.app `i_to_expr [`p]))])))))
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
                     (termIfThenElse
                      "if"
                      `e
                      "then"
                      (Term.app `pure [`e])
                      "else"
                      («term_>>_» (Term.app `tactic.generalize [`e]) ">>" `intro1)))))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doPatDecl
                    (Term.tuple "(" [`e "," [`newvars "," `locals]] ")")
                    "←"
                    (Term.doExpr
                     (Term.do
                      "do"
                      (Term.doSeqIndent
                       [(Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doPatDecl
                           `none
                           "←"
                           (Term.doExpr (Term.app `pure [`rec_name]))
                           ["|"
                            (Term.doSeqIndent
                             [(Term.doSeqItem
                               (Term.doExpr
                                (Term.app
                                 `pure
                                 [(Term.tuple
                                   "("
                                   [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                                   ")")]))
                               [])])]))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `whnf_ginductive [`t]))))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doPatDecl
                           (Term.app `const [`n (Term.hole "_")])
                           "←"
                           (Term.doExpr (Term.app `pure [`t]))
                           ["|"
                            (Term.doSeqIndent
                             [(Term.doSeqItem
                               (Term.doExpr
                                (Term.app
                                 `pure
                                 [(Term.tuple
                                   "("
                                   [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                                   ")")]))
                               [])])]))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl `env [] "←" (Term.doExpr `get_env)))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doPatDecl
                           `tt
                           "←"
                           (Term.doExpr («term_<|_» `pure "<|" (Term.app `env [`n])))
                           ["|"
                            (Term.doSeqIndent
                             [(Term.doSeqItem
                               (Term.doExpr
                                (Term.app
                                 `pure
                                 [(Term.tuple
                                   "("
                                   [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                                   ")")]))
                               [])])]))
                         [])
                        (Term.doSeqItem
                         (Term.doLet
                          "let"
                          []
                          (Term.letDecl
                           (Term.letPatDecl
                            (Term.tuple "(" [`locals "," [`nonlocals]] ")")
                            []
                            []
                            ":="
                            (Term.app
                             (Term.proj («term_<|_» `t "<|" (Term.app `env [`n])) "." `partition)
                             [(Term.fun
                               "fun"
                               (Term.basicFun [`arg] [(Term.typeSpec ":" `expr)] "=>" `arg))]))))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doPatDecl
                           («term_::_» (Term.hole "_") "::" (Term.hole "_"))
                           "←"
                           (Term.doExpr (Term.app `pure [`nonlocals]))
                           ["|"
                            (Term.doSeqIndent
                             [(Term.doSeqItem
                               (Term.doExpr
                                (Term.app
                                 `pure
                                 [(Term.tuple
                                   "("
                                   [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                                   ")")]))
                               [])])]))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `tactic.revert [`e]))))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow
                          "let"
                          []
                          (Term.doIdDecl
                           `newvars
                           []
                           "←"
                           (Term.doExpr
                            (Term.app
                             `nonlocals
                             [(Term.fun
                               "fun"
                               (Term.basicFun
                                [`arg]
                                []
                                "=>"
                                (Term.do
                                 "do"
                                 (Term.doSeqIndent
                                  [(Term.doSeqItem
                                    (Term.doLetArrow
                                     "let"
                                     []
                                     (Term.doIdDecl
                                      `n
                                      []
                                      "←"
                                      (Term.doExpr (Term.app `revert_kdeps [`arg]))))
                                    [])
                                   (Term.doSeqItem
                                    (Term.doExpr (Term.app `tactic.generalize [`arg]))
                                    [])
                                   (Term.doSeqItem
                                    (Term.doLetArrow
                                     "let"
                                     []
                                     (Term.doIdDecl `h [] "←" (Term.doExpr `intro1)))
                                    [])
                                   (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])
                                   (Term.doSeqItem
                                    (Term.doLet
                                     "let"
                                     []
                                     (Term.letDecl
                                      (Term.letIdDecl
                                       `locals
                                       []
                                       []
                                       ":="
                                       (Term.app
                                        `arg
                                        [(«term[_]» "[" [] "]")
                                         (Term.fun
                                          "fun"
                                          (Term.basicFun
                                           [`e (Term.hole "_") `acc]
                                           []
                                           "=>"
                                           (termIfThenElse
                                            "if"
                                            `e
                                            "then"
                                            («term_::_» `e "::" `Acc)
                                            "else"
                                            `Acc)))]))))
                                    [])
                                   (Term.doSeqItem
                                    (Term.doExpr (Term.app `locals [(«term_∘_» `try "∘" `clear)]))
                                    [])
                                   (Term.doSeqItem (Term.doExpr (Term.app `pure [`h])) [])]))))]))))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))]))
                         [])
                        (Term.doSeqItem
                         (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr `intro1)))
                         [])
                        (Term.doSeqItem
                         (Term.doExpr
                          (Term.app `pure [(Term.tuple "(" [`e "," [`newvars "," `locals]] ")")]))
                         [])])))
                    []))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl
                    `to_generalize
                    []
                    "←"
                    (Term.doExpr
                     (Term.app
                      (Term.proj (Term.app `revert [(«term[_]» "[" [] "]")]) "." `mmap)
                      [`tactic.get_local]))))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl
                    `num_generalized
                    []
                    "←"
                    (Term.doExpr (Term.app `revert_lst [`to_generalize]))))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl
                    `rs
                    []
                    "←"
                    (Term.doExpr (Term.app `tactic.induction [`e `ids `rec_name]))))
                  [])
                 (Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doIdDecl
                    `gen_hyps
                    []
                    "←"
                    (Term.doExpr
                     (Term.app
                      `all_goals
                      [(Term.do
                        "do"
                        (Term.doSeqIndent
                         [(Term.doSeqItem
                           (Term.doLetArrow
                            "let"
                            []
                            (Term.doIdDecl
                             `new_hyps
                             []
                             "←"
                             (Term.doExpr (Term.app `intron' [`num_generalized]))))
                           [])
                          (Term.doSeqItem
                           (Term.doExpr
                            (Term.app `clear_lst [(Term.app `newvars [`local_pp_name])]))
                           [])
                          (Term.doSeqItem
                           (Term.doExpr
                            (Term.app
                             (Term.proj («term_::_» `e "::" `locals) "." `mmap')
                             [(«term_∘_» `try "∘" `clear)]))
                           [])
                          (Term.doSeqItem (Term.doExpr (Term.app `pure [`new_hyps])) [])]))]))))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr
                   («term_<|_»
                    (Term.app `set_cases_tags [`in_tag])
                    "<|"
                    (Term.app
                     (Term.explicit "@" `List.map₂)
                     [(«term_×_»
                       `Name
                       "×"
                       («term_×_»
                        (Term.app `List [`expr])
                        "×"
                        (Term.app `List [(«term_×_» `Name "×" `expr)])))
                      (Term.hole "_")
                      («term_×_» `Name "×" (Term.app `List [`expr]))
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.anonymousCtor "⟨" [`n "," `hyps "," (Term.hole "_")] "⟩") `gen_hyps]
                        []
                        "=>"
                        (Term.anonymousCtor "⟨" [`n "," («term_++_» `hyps "++" `gen_hyps)] "⟩")))
                      `rs
                      `gen_hyps])))
                  [])]))]))
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
          (Term.doLetArrow "let" [] (Term.doIdDecl `in_tag [] "←" (Term.doExpr `get_main_tag)))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `focus1
            [(Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `e
                   []
                   "←"
                   (Term.doExpr
                    (Term.match
                     "match"
                     []
                     []
                     [(Term.matchDiscr [] `hp)]
                     "with"
                     (Term.matchAlts
                      [(Term.matchAlt
                        "|"
                        [[(Term.tuple "(" [(Term.app `some [`h]) "," [`p]] ")")]]
                        "=>"
                        (Term.do
                         "do"
                         (Term.doSeqIndent
                          [(Term.doSeqItem
                            (Term.doLetArrow
                             "let"
                             []
                             (Term.doIdDecl `x [] "←" (Term.doExpr `get_unused_name)))
                            [])
                           (Term.doSeqItem
                            (Term.doExpr
                             (Term.app
                              `generalize
                              [`h (Term.tuple "(" [] ")") (Term.tuple "(" [`p "," [`x]] ")")]))
                            [])
                           (Term.doSeqItem (Term.doExpr (Term.app `get_local [`x])) [])])))
                       (Term.matchAlt
                        "|"
                        [[(Term.tuple "(" [`none "," [`p]] ")")]]
                        "=>"
                        (Term.app `i_to_expr [`p]))])))))
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
                    (termIfThenElse
                     "if"
                     `e
                     "then"
                     (Term.app `pure [`e])
                     "else"
                     («term_>>_» (Term.app `tactic.generalize [`e]) ">>" `intro1)))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`e "," [`newvars "," `locals]] ")")
                   "←"
                   (Term.doExpr
                    (Term.do
                     "do"
                     (Term.doSeqIndent
                      [(Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doPatDecl
                          `none
                          "←"
                          (Term.doExpr (Term.app `pure [`rec_name]))
                          ["|"
                           (Term.doSeqIndent
                            [(Term.doSeqItem
                              (Term.doExpr
                               (Term.app
                                `pure
                                [(Term.tuple
                                  "("
                                  [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                                  ")")]))
                              [])])]))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `whnf_ginductive [`t]))))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doPatDecl
                          (Term.app `const [`n (Term.hole "_")])
                          "←"
                          (Term.doExpr (Term.app `pure [`t]))
                          ["|"
                           (Term.doSeqIndent
                            [(Term.doSeqItem
                              (Term.doExpr
                               (Term.app
                                `pure
                                [(Term.tuple
                                  "("
                                  [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                                  ")")]))
                              [])])]))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `env [] "←" (Term.doExpr `get_env)))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doPatDecl
                          `tt
                          "←"
                          (Term.doExpr («term_<|_» `pure "<|" (Term.app `env [`n])))
                          ["|"
                           (Term.doSeqIndent
                            [(Term.doSeqItem
                              (Term.doExpr
                               (Term.app
                                `pure
                                [(Term.tuple
                                  "("
                                  [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                                  ")")]))
                              [])])]))
                        [])
                       (Term.doSeqItem
                        (Term.doLet
                         "let"
                         []
                         (Term.letDecl
                          (Term.letPatDecl
                           (Term.tuple "(" [`locals "," [`nonlocals]] ")")
                           []
                           []
                           ":="
                           (Term.app
                            (Term.proj («term_<|_» `t "<|" (Term.app `env [`n])) "." `partition)
                            [(Term.fun
                              "fun"
                              (Term.basicFun [`arg] [(Term.typeSpec ":" `expr)] "=>" `arg))]))))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doPatDecl
                          («term_::_» (Term.hole "_") "::" (Term.hole "_"))
                          "←"
                          (Term.doExpr (Term.app `pure [`nonlocals]))
                          ["|"
                           (Term.doSeqIndent
                            [(Term.doSeqItem
                              (Term.doExpr
                               (Term.app
                                `pure
                                [(Term.tuple
                                  "("
                                  [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                                  ")")]))
                              [])])]))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `tactic.revert [`e]))))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow
                         "let"
                         []
                         (Term.doIdDecl
                          `newvars
                          []
                          "←"
                          (Term.doExpr
                           (Term.app
                            `nonlocals
                            [(Term.fun
                              "fun"
                              (Term.basicFun
                               [`arg]
                               []
                               "=>"
                               (Term.do
                                "do"
                                (Term.doSeqIndent
                                 [(Term.doSeqItem
                                   (Term.doLetArrow
                                    "let"
                                    []
                                    (Term.doIdDecl
                                     `n
                                     []
                                     "←"
                                     (Term.doExpr (Term.app `revert_kdeps [`arg]))))
                                   [])
                                  (Term.doSeqItem
                                   (Term.doExpr (Term.app `tactic.generalize [`arg]))
                                   [])
                                  (Term.doSeqItem
                                   (Term.doLetArrow
                                    "let"
                                    []
                                    (Term.doIdDecl `h [] "←" (Term.doExpr `intro1)))
                                   [])
                                  (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])
                                  (Term.doSeqItem
                                   (Term.doLet
                                    "let"
                                    []
                                    (Term.letDecl
                                     (Term.letIdDecl
                                      `locals
                                      []
                                      []
                                      ":="
                                      (Term.app
                                       `arg
                                       [(«term[_]» "[" [] "]")
                                        (Term.fun
                                         "fun"
                                         (Term.basicFun
                                          [`e (Term.hole "_") `acc]
                                          []
                                          "=>"
                                          (termIfThenElse
                                           "if"
                                           `e
                                           "then"
                                           («term_::_» `e "::" `Acc)
                                           "else"
                                           `Acc)))]))))
                                   [])
                                  (Term.doSeqItem
                                   (Term.doExpr (Term.app `locals [(«term_∘_» `try "∘" `clear)]))
                                   [])
                                  (Term.doSeqItem (Term.doExpr (Term.app `pure [`h])) [])]))))]))))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))]))
                        [])
                       (Term.doSeqItem
                        (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr `intro1)))
                        [])
                       (Term.doSeqItem
                        (Term.doExpr
                         (Term.app `pure [(Term.tuple "(" [`e "," [`newvars "," `locals]] ")")]))
                        [])])))
                   []))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `to_generalize
                   []
                   "←"
                   (Term.doExpr
                    (Term.app
                     (Term.proj (Term.app `revert [(«term[_]» "[" [] "]")]) "." `mmap)
                     [`tactic.get_local]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `num_generalized
                   []
                   "←"
                   (Term.doExpr (Term.app `revert_lst [`to_generalize]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `rs
                   []
                   "←"
                   (Term.doExpr (Term.app `tactic.induction [`e `ids `rec_name]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `gen_hyps
                   []
                   "←"
                   (Term.doExpr
                    (Term.app
                     `all_goals
                     [(Term.do
                       "do"
                       (Term.doSeqIndent
                        [(Term.doSeqItem
                          (Term.doLetArrow
                           "let"
                           []
                           (Term.doIdDecl
                            `new_hyps
                            []
                            "←"
                            (Term.doExpr (Term.app `intron' [`num_generalized]))))
                          [])
                         (Term.doSeqItem
                          (Term.doExpr (Term.app `clear_lst [(Term.app `newvars [`local_pp_name])]))
                          [])
                         (Term.doSeqItem
                          (Term.doExpr
                           (Term.app
                            (Term.proj («term_::_» `e "::" `locals) "." `mmap')
                            [(«term_∘_» `try "∘" `clear)]))
                          [])
                         (Term.doSeqItem (Term.doExpr (Term.app `pure [`new_hyps])) [])]))]))))
                 [])
                (Term.doSeqItem
                 (Term.doExpr
                  («term_<|_»
                   (Term.app `set_cases_tags [`in_tag])
                   "<|"
                   (Term.app
                    (Term.explicit "@" `List.map₂)
                    [(«term_×_»
                      `Name
                      "×"
                      («term_×_»
                       (Term.app `List [`expr])
                       "×"
                       (Term.app `List [(«term_×_» `Name "×" `expr)])))
                     (Term.hole "_")
                     («term_×_» `Name "×" (Term.app `List [`expr]))
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor "⟨" [`n "," `hyps "," (Term.hole "_")] "⟩") `gen_hyps]
                       []
                       "=>"
                       (Term.anonymousCtor "⟨" [`n "," («term_++_» `hyps "++" `gen_hyps)] "⟩")))
                     `rs
                     `gen_hyps])))
                 [])]))]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `focus1
       [(Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl
              `e
              []
              "←"
              (Term.doExpr
               (Term.match
                "match"
                []
                []
                [(Term.matchDiscr [] `hp)]
                "with"
                (Term.matchAlts
                 [(Term.matchAlt
                   "|"
                   [[(Term.tuple "(" [(Term.app `some [`h]) "," [`p]] ")")]]
                   "=>"
                   (Term.do
                    "do"
                    (Term.doSeqIndent
                     [(Term.doSeqItem
                       (Term.doLetArrow
                        "let"
                        []
                        (Term.doIdDecl `x [] "←" (Term.doExpr `get_unused_name)))
                       [])
                      (Term.doSeqItem
                       (Term.doExpr
                        (Term.app
                         `generalize
                         [`h (Term.tuple "(" [] ")") (Term.tuple "(" [`p "," [`x]] ")")]))
                       [])
                      (Term.doSeqItem (Term.doExpr (Term.app `get_local [`x])) [])])))
                  (Term.matchAlt
                   "|"
                   [[(Term.tuple "(" [`none "," [`p]] ")")]]
                   "=>"
                   (Term.app `i_to_expr [`p]))])))))
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
               (termIfThenElse
                "if"
                `e
                "then"
                (Term.app `pure [`e])
                "else"
                («term_>>_» (Term.app `tactic.generalize [`e]) ">>" `intro1)))))
            [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doPatDecl
              (Term.tuple "(" [`e "," [`newvars "," `locals]] ")")
              "←"
              (Term.doExpr
               (Term.do
                "do"
                (Term.doSeqIndent
                 [(Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doPatDecl
                     `none
                     "←"
                     (Term.doExpr (Term.app `pure [`rec_name]))
                     ["|"
                      (Term.doSeqIndent
                       [(Term.doSeqItem
                         (Term.doExpr
                          (Term.app
                           `pure
                           [(Term.tuple
                             "("
                             [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                             ")")]))
                         [])])]))
                   [])
                  (Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                   [])
                  (Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `whnf_ginductive [`t]))))
                   [])
                  (Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doPatDecl
                     (Term.app `const [`n (Term.hole "_")])
                     "←"
                     (Term.doExpr (Term.app `pure [`t]))
                     ["|"
                      (Term.doSeqIndent
                       [(Term.doSeqItem
                         (Term.doExpr
                          (Term.app
                           `pure
                           [(Term.tuple
                             "("
                             [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                             ")")]))
                         [])])]))
                   [])
                  (Term.doSeqItem
                   (Term.doLetArrow "let" [] (Term.doIdDecl `env [] "←" (Term.doExpr `get_env)))
                   [])
                  (Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doPatDecl
                     `tt
                     "←"
                     (Term.doExpr («term_<|_» `pure "<|" (Term.app `env [`n])))
                     ["|"
                      (Term.doSeqIndent
                       [(Term.doSeqItem
                         (Term.doExpr
                          (Term.app
                           `pure
                           [(Term.tuple
                             "("
                             [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                             ")")]))
                         [])])]))
                   [])
                  (Term.doSeqItem
                   (Term.doLet
                    "let"
                    []
                    (Term.letDecl
                     (Term.letPatDecl
                      (Term.tuple "(" [`locals "," [`nonlocals]] ")")
                      []
                      []
                      ":="
                      (Term.app
                       (Term.proj («term_<|_» `t "<|" (Term.app `env [`n])) "." `partition)
                       [(Term.fun
                         "fun"
                         (Term.basicFun [`arg] [(Term.typeSpec ":" `expr)] "=>" `arg))]))))
                   [])
                  (Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doPatDecl
                     («term_::_» (Term.hole "_") "::" (Term.hole "_"))
                     "←"
                     (Term.doExpr (Term.app `pure [`nonlocals]))
                     ["|"
                      (Term.doSeqIndent
                       [(Term.doSeqItem
                         (Term.doExpr
                          (Term.app
                           `pure
                           [(Term.tuple
                             "("
                             [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                             ")")]))
                         [])])]))
                   [])
                  (Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `tactic.revert [`e]))))
                   [])
                  (Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doIdDecl
                     `newvars
                     []
                     "←"
                     (Term.doExpr
                      (Term.app
                       `nonlocals
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`arg]
                          []
                          "=>"
                          (Term.do
                           "do"
                           (Term.doSeqIndent
                            [(Term.doSeqItem
                              (Term.doLetArrow
                               "let"
                               []
                               (Term.doIdDecl
                                `n
                                []
                                "←"
                                (Term.doExpr (Term.app `revert_kdeps [`arg]))))
                              [])
                             (Term.doSeqItem (Term.doExpr (Term.app `tactic.generalize [`arg])) [])
                             (Term.doSeqItem
                              (Term.doLetArrow
                               "let"
                               []
                               (Term.doIdDecl `h [] "←" (Term.doExpr `intro1)))
                              [])
                             (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])
                             (Term.doSeqItem
                              (Term.doLet
                               "let"
                               []
                               (Term.letDecl
                                (Term.letIdDecl
                                 `locals
                                 []
                                 []
                                 ":="
                                 (Term.app
                                  `arg
                                  [(«term[_]» "[" [] "]")
                                   (Term.fun
                                    "fun"
                                    (Term.basicFun
                                     [`e (Term.hole "_") `acc]
                                     []
                                     "=>"
                                     (termIfThenElse
                                      "if"
                                      `e
                                      "then"
                                      («term_::_» `e "::" `Acc)
                                      "else"
                                      `Acc)))]))))
                              [])
                             (Term.doSeqItem
                              (Term.doExpr (Term.app `locals [(«term_∘_» `try "∘" `clear)]))
                              [])
                             (Term.doSeqItem (Term.doExpr (Term.app `pure [`h])) [])]))))]))))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))]))
                   [])
                  (Term.doSeqItem
                   (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr `intro1)))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr
                    (Term.app `pure [(Term.tuple "(" [`e "," [`newvars "," `locals]] ")")]))
                   [])])))
              []))
            [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl
              `to_generalize
              []
              "←"
              (Term.doExpr
               (Term.app
                (Term.proj (Term.app `revert [(«term[_]» "[" [] "]")]) "." `mmap)
                [`tactic.get_local]))))
            [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl
              `num_generalized
              []
              "←"
              (Term.doExpr (Term.app `revert_lst [`to_generalize]))))
            [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl
              `rs
              []
              "←"
              (Term.doExpr (Term.app `tactic.induction [`e `ids `rec_name]))))
            [])
           (Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl
              `gen_hyps
              []
              "←"
              (Term.doExpr
               (Term.app
                `all_goals
                [(Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doIdDecl
                       `new_hyps
                       []
                       "←"
                       (Term.doExpr (Term.app `intron' [`num_generalized]))))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr (Term.app `clear_lst [(Term.app `newvars [`local_pp_name])]))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr
                      (Term.app
                       (Term.proj («term_::_» `e "::" `locals) "." `mmap')
                       [(«term_∘_» `try "∘" `clear)]))
                     [])
                    (Term.doSeqItem (Term.doExpr (Term.app `pure [`new_hyps])) [])]))]))))
            [])
           (Term.doSeqItem
            (Term.doExpr
             («term_<|_»
              (Term.app `set_cases_tags [`in_tag])
              "<|"
              (Term.app
               (Term.explicit "@" `List.map₂)
               [(«term_×_»
                 `Name
                 "×"
                 («term_×_»
                  (Term.app `List [`expr])
                  "×"
                  (Term.app `List [(«term_×_» `Name "×" `expr)])))
                (Term.hole "_")
                («term_×_» `Name "×" (Term.app `List [`expr]))
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.anonymousCtor "⟨" [`n "," `hyps "," (Term.hole "_")] "⟩") `gen_hyps]
                  []
                  "=>"
                  (Term.anonymousCtor "⟨" [`n "," («term_++_» `hyps "++" `gen_hyps)] "⟩")))
                `rs
                `gen_hyps])))
            [])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `e
            []
            "←"
            (Term.doExpr
             (Term.match
              "match"
              []
              []
              [(Term.matchDiscr [] `hp)]
              "with"
              (Term.matchAlts
               [(Term.matchAlt
                 "|"
                 [[(Term.tuple "(" [(Term.app `some [`h]) "," [`p]] ")")]]
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doIdDecl `x [] "←" (Term.doExpr `get_unused_name)))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr
                      (Term.app
                       `generalize
                       [`h (Term.tuple "(" [] ")") (Term.tuple "(" [`p "," [`x]] ")")]))
                     [])
                    (Term.doSeqItem (Term.doExpr (Term.app `get_local [`x])) [])])))
                (Term.matchAlt
                 "|"
                 [[(Term.tuple "(" [`none "," [`p]] ")")]]
                 "=>"
                 (Term.app `i_to_expr [`p]))])))))
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
             (termIfThenElse
              "if"
              `e
              "then"
              (Term.app `pure [`e])
              "else"
              («term_>>_» (Term.app `tactic.generalize [`e]) ">>" `intro1)))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`e "," [`newvars "," `locals]] ")")
            "←"
            (Term.doExpr
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   `none
                   "←"
                   (Term.doExpr (Term.app `pure [`rec_name]))
                   ["|"
                    (Term.doSeqIndent
                     [(Term.doSeqItem
                       (Term.doExpr
                        (Term.app
                         `pure
                         [(Term.tuple
                           "("
                           [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                           ")")]))
                       [])])]))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `whnf_ginductive [`t]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.app `const [`n (Term.hole "_")])
                   "←"
                   (Term.doExpr (Term.app `pure [`t]))
                   ["|"
                    (Term.doSeqIndent
                     [(Term.doSeqItem
                       (Term.doExpr
                        (Term.app
                         `pure
                         [(Term.tuple
                           "("
                           [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                           ")")]))
                       [])])]))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow "let" [] (Term.doIdDecl `env [] "←" (Term.doExpr `get_env)))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   `tt
                   "←"
                   (Term.doExpr («term_<|_» `pure "<|" (Term.app `env [`n])))
                   ["|"
                    (Term.doSeqIndent
                     [(Term.doSeqItem
                       (Term.doExpr
                        (Term.app
                         `pure
                         [(Term.tuple
                           "("
                           [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                           ")")]))
                       [])])]))
                 [])
                (Term.doSeqItem
                 (Term.doLet
                  "let"
                  []
                  (Term.letDecl
                   (Term.letPatDecl
                    (Term.tuple "(" [`locals "," [`nonlocals]] ")")
                    []
                    []
                    ":="
                    (Term.app
                     (Term.proj («term_<|_» `t "<|" (Term.app `env [`n])) "." `partition)
                     [(Term.fun
                       "fun"
                       (Term.basicFun [`arg] [(Term.typeSpec ":" `expr)] "=>" `arg))]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   («term_::_» (Term.hole "_") "::" (Term.hole "_"))
                   "←"
                   (Term.doExpr (Term.app `pure [`nonlocals]))
                   ["|"
                    (Term.doSeqIndent
                     [(Term.doSeqItem
                       (Term.doExpr
                        (Term.app
                         `pure
                         [(Term.tuple
                           "("
                           [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                           ")")]))
                       [])])]))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `tactic.revert [`e]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `newvars
                   []
                   "←"
                   (Term.doExpr
                    (Term.app
                     `nonlocals
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`arg]
                        []
                        "=>"
                        (Term.do
                         "do"
                         (Term.doSeqIndent
                          [(Term.doSeqItem
                            (Term.doLetArrow
                             "let"
                             []
                             (Term.doIdDecl
                              `n
                              []
                              "←"
                              (Term.doExpr (Term.app `revert_kdeps [`arg]))))
                            [])
                           (Term.doSeqItem (Term.doExpr (Term.app `tactic.generalize [`arg])) [])
                           (Term.doSeqItem
                            (Term.doLetArrow
                             "let"
                             []
                             (Term.doIdDecl `h [] "←" (Term.doExpr `intro1)))
                            [])
                           (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])
                           (Term.doSeqItem
                            (Term.doLet
                             "let"
                             []
                             (Term.letDecl
                              (Term.letIdDecl
                               `locals
                               []
                               []
                               ":="
                               (Term.app
                                `arg
                                [(«term[_]» "[" [] "]")
                                 (Term.fun
                                  "fun"
                                  (Term.basicFun
                                   [`e (Term.hole "_") `acc]
                                   []
                                   "=>"
                                   (termIfThenElse
                                    "if"
                                    `e
                                    "then"
                                    («term_::_» `e "::" `Acc)
                                    "else"
                                    `Acc)))]))))
                            [])
                           (Term.doSeqItem
                            (Term.doExpr (Term.app `locals [(«term_∘_» `try "∘" `clear)]))
                            [])
                           (Term.doSeqItem (Term.doExpr (Term.app `pure [`h])) [])]))))]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))])) [])
                (Term.doSeqItem
                 (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr `intro1)))
                 [])
                (Term.doSeqItem
                 (Term.doExpr
                  (Term.app `pure [(Term.tuple "(" [`e "," [`newvars "," `locals]] ")")]))
                 [])])))
            []))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `to_generalize
            []
            "←"
            (Term.doExpr
             (Term.app
              (Term.proj (Term.app `revert [(«term[_]» "[" [] "]")]) "." `mmap)
              [`tactic.get_local]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `num_generalized
            []
            "←"
            (Term.doExpr (Term.app `revert_lst [`to_generalize]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `rs
            []
            "←"
            (Term.doExpr (Term.app `tactic.induction [`e `ids `rec_name]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `gen_hyps
            []
            "←"
            (Term.doExpr
             (Term.app
              `all_goals
              [(Term.do
                "do"
                (Term.doSeqIndent
                 [(Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doIdDecl
                     `new_hyps
                     []
                     "←"
                     (Term.doExpr (Term.app `intron' [`num_generalized]))))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr (Term.app `clear_lst [(Term.app `newvars [`local_pp_name])]))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr
                    (Term.app
                     (Term.proj («term_::_» `e "::" `locals) "." `mmap')
                     [(«term_∘_» `try "∘" `clear)]))
                   [])
                  (Term.doSeqItem (Term.doExpr (Term.app `pure [`new_hyps])) [])]))]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           («term_<|_»
            (Term.app `set_cases_tags [`in_tag])
            "<|"
            (Term.app
             (Term.explicit "@" `List.map₂)
             [(«term_×_»
               `Name
               "×"
               («term_×_»
                (Term.app `List [`expr])
                "×"
                (Term.app `List [(«term_×_» `Name "×" `expr)])))
              (Term.hole "_")
              («term_×_» `Name "×" (Term.app `List [`expr]))
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.anonymousCtor "⟨" [`n "," `hyps "," (Term.hole "_")] "⟩") `gen_hyps]
                []
                "=>"
                (Term.anonymousCtor "⟨" [`n "," («term_++_» `hyps "++" `gen_hyps)] "⟩")))
              `rs
              `gen_hyps])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `set_cases_tags [`in_tag])
       "<|"
       (Term.app
        (Term.explicit "@" `List.map₂)
        [(«term_×_»
          `Name
          "×"
          («term_×_» (Term.app `List [`expr]) "×" (Term.app `List [(«term_×_» `Name "×" `expr)])))
         (Term.hole "_")
         («term_×_» `Name "×" (Term.app `List [`expr]))
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [`n "," `hyps "," (Term.hole "_")] "⟩") `gen_hyps]
           []
           "=>"
           (Term.anonymousCtor "⟨" [`n "," («term_++_» `hyps "++" `gen_hyps)] "⟩")))
         `rs
         `gen_hyps]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `List.map₂)
       [(«term_×_»
         `Name
         "×"
         («term_×_» (Term.app `List [`expr]) "×" (Term.app `List [(«term_×_» `Name "×" `expr)])))
        (Term.hole "_")
        («term_×_» `Name "×" (Term.app `List [`expr]))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`n "," `hyps "," (Term.hole "_")] "⟩") `gen_hyps]
          []
          "=>"
          (Term.anonymousCtor "⟨" [`n "," («term_++_» `hyps "++" `gen_hyps)] "⟩")))
        `rs
        `gen_hyps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gen_hyps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `rs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`n "," `hyps "," (Term.hole "_")] "⟩") `gen_hyps]
        []
        "=>"
        (Term.anonymousCtor "⟨" [`n "," («term_++_» `hyps "++" `gen_hyps)] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`n "," («term_++_» `hyps "++" `gen_hyps)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_» `hyps "++" `gen_hyps)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gen_hyps
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `hyps
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gen_hyps
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.anonymousCtor "⟨" [`n "," `hyps "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hyps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.anonymousCtor "⟨" [`n "," `hyps "," (Term.hole "_")] "⟩") `gen_hyps]
       []
       "=>"
       (Term.anonymousCtor "⟨" [`n "," («term_++_» `hyps "++" `gen_hyps)] "⟩")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_×_» `Name "×" (Term.app `List [`expr]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `List [`expr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `expr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `List
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `Name
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 35, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_×_» `Name "×" (Term.app `List [`expr]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term_×_»
       `Name
       "×"
       («term_×_» (Term.app `List [`expr]) "×" (Term.app `List [(«term_×_» `Name "×" `expr)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» (Term.app `List [`expr]) "×" (Term.app `List [(«term_×_» `Name "×" `expr)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `List [(«term_×_» `Name "×" `expr)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» `Name "×" `expr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `expr
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `Name
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_×_» `Name "×" `expr) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `List
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app `List [`expr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `expr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `List
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `Name
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 35, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_×_»
      `Name
      "×"
      («term_×_»
       (Term.app `List [`expr])
       "×"
       (Term.app `List [(Term.paren "(" («term_×_» `Name "×" `expr) ")")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `List.map₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `List.map₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `set_cases_tags [`in_tag])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `in_tag
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_cases_tags
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `all_goals
       [(Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl `new_hyps [] "←" (Term.doExpr (Term.app `intron' [`num_generalized]))))
            [])
           (Term.doSeqItem
            (Term.doExpr (Term.app `clear_lst [(Term.app `newvars [`local_pp_name])]))
            [])
           (Term.doSeqItem
            (Term.doExpr
             (Term.app
              (Term.proj («term_::_» `e "::" `locals) "." `mmap')
              [(«term_∘_» `try "∘" `clear)]))
            [])
           (Term.doSeqItem (Term.doExpr (Term.app `pure [`new_hyps])) [])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `new_hyps [] "←" (Term.doExpr (Term.app `intron' [`num_generalized]))))
          [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `clear_lst [(Term.app `newvars [`local_pp_name])]))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            (Term.proj («term_::_» `e "::" `locals) "." `mmap')
            [(«term_∘_» `try "∘" `clear)]))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `pure [`new_hyps])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`new_hyps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `new_hyps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app (Term.proj («term_::_» `e "::" `locals) "." `mmap') [(«term_∘_» `try "∘" `clear)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `try "∘" `clear)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `clear
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `try
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `try "∘" `clear) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_::_» `e "::" `locals) "." `mmap')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_::_» `e "::" `locals)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `locals
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_::_» `e "::" `locals) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `clear_lst [(Term.app `newvars [`local_pp_name])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `newvars [`local_pp_name])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `local_pp_name
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `newvars
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `newvars [`local_pp_name])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `clear_lst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `intron' [`num_generalized])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `num_generalized
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intron'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `all_goals
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `tactic.induction [`e `ids `rec_name])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rec_name
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
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.induction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `revert_lst [`to_generalize])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_generalize
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `revert_lst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       (Term.proj (Term.app `revert [(«term[_]» "[" [] "]")]) "." `mmap)
       [`tactic.get_local])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.get_local
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `revert [(«term[_]» "[" [] "]")]) "." `mmap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `revert [(«term[_]» "[" [] "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `revert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `revert [(«term[_]» "[" [] "]")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            `none
            "←"
            (Term.doExpr (Term.app `pure [`rec_name]))
            ["|"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doExpr
                 (Term.app
                  `pure
                  [(Term.tuple
                    "("
                    [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                    ")")]))
                [])])]))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `infer_type [`e]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `t [] "←" (Term.doExpr (Term.app `whnf_ginductive [`t]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.app `const [`n (Term.hole "_")])
            "←"
            (Term.doExpr (Term.app `pure [`t]))
            ["|"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doExpr
                 (Term.app
                  `pure
                  [(Term.tuple
                    "("
                    [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                    ")")]))
                [])])]))
          [])
         (Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `env [] "←" (Term.doExpr `get_env)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            `tt
            "←"
            (Term.doExpr («term_<|_» `pure "<|" (Term.app `env [`n])))
            ["|"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doExpr
                 (Term.app
                  `pure
                  [(Term.tuple
                    "("
                    [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                    ")")]))
                [])])]))
          [])
         (Term.doSeqItem
          (Term.doLet
           "let"
           []
           (Term.letDecl
            (Term.letPatDecl
             (Term.tuple "(" [`locals "," [`nonlocals]] ")")
             []
             []
             ":="
             (Term.app
              (Term.proj («term_<|_» `t "<|" (Term.app `env [`n])) "." `partition)
              [(Term.fun "fun" (Term.basicFun [`arg] [(Term.typeSpec ":" `expr)] "=>" `arg))]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            («term_::_» (Term.hole "_") "::" (Term.hole "_"))
            "←"
            (Term.doExpr (Term.app `pure [`nonlocals]))
            ["|"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doExpr
                 (Term.app
                  `pure
                  [(Term.tuple
                    "("
                    [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
                    ")")]))
                [])])]))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `tactic.revert [`e]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `newvars
            []
            "←"
            (Term.doExpr
             (Term.app
              `nonlocals
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`arg]
                 []
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert_kdeps [`arg]))))
                     [])
                    (Term.doSeqItem (Term.doExpr (Term.app `tactic.generalize [`arg])) [])
                    (Term.doSeqItem
                     (Term.doLetArrow "let" [] (Term.doIdDecl `h [] "←" (Term.doExpr `intro1)))
                     [])
                    (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])
                    (Term.doSeqItem
                     (Term.doLet
                      "let"
                      []
                      (Term.letDecl
                       (Term.letIdDecl
                        `locals
                        []
                        []
                        ":="
                        (Term.app
                         `arg
                         [(«term[_]» "[" [] "]")
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`e (Term.hole "_") `acc]
                            []
                            "=>"
                            (termIfThenElse
                             "if"
                             `e
                             "then"
                             («term_::_» `e "::" `Acc)
                             "else"
                             `Acc)))]))))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr (Term.app `locals [(«term_∘_» `try "∘" `clear)]))
                     [])
                    (Term.doSeqItem (Term.doExpr (Term.app `pure [`h])) [])]))))]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `intron [(«term_-_» `n "-" (num "1"))])) [])
         (Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `e [] "←" (Term.doExpr `intro1)))
          [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `pure [(Term.tuple "(" [`e "," [`newvars "," `locals]] ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [(Term.tuple "(" [`e "," [`newvars "," `locals]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`e "," [`newvars "," `locals]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `locals
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `newvars
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `intro1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `intron [(«term_-_» `n "-" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `n "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `n "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intron
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `nonlocals
       [(Term.fun
         "fun"
         (Term.basicFun
          [`arg]
          []
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert_kdeps [`arg]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `tactic.generalize [`arg])) [])
             (Term.doSeqItem
              (Term.doLetArrow "let" [] (Term.doIdDecl `h [] "←" (Term.doExpr `intro1)))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])
             (Term.doSeqItem
              (Term.doLet
               "let"
               []
               (Term.letDecl
                (Term.letIdDecl
                 `locals
                 []
                 []
                 ":="
                 (Term.app
                  `arg
                  [(«term[_]» "[" [] "]")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`e (Term.hole "_") `acc]
                     []
                     "=>"
                     (termIfThenElse "if" `e "then" («term_::_» `e "::" `Acc) "else" `Acc)))]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `locals [(«term_∘_» `try "∘" `clear)])) [])
             (Term.doSeqItem (Term.doExpr (Term.app `pure [`h])) [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`arg]
        []
        "=>"
        (Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert_kdeps [`arg]))))
            [])
           (Term.doSeqItem (Term.doExpr (Term.app `tactic.generalize [`arg])) [])
           (Term.doSeqItem
            (Term.doLetArrow "let" [] (Term.doIdDecl `h [] "←" (Term.doExpr `intro1)))
            [])
           (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])
           (Term.doSeqItem
            (Term.doLet
             "let"
             []
             (Term.letDecl
              (Term.letIdDecl
               `locals
               []
               []
               ":="
               (Term.app
                `arg
                [(«term[_]» "[" [] "]")
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`e (Term.hole "_") `acc]
                   []
                   "=>"
                   (termIfThenElse "if" `e "then" («term_::_» `e "::" `Acc) "else" `Acc)))]))))
            [])
           (Term.doSeqItem (Term.doExpr (Term.app `locals [(«term_∘_» `try "∘" `clear)])) [])
           (Term.doSeqItem (Term.doExpr (Term.app `pure [`h])) [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert_kdeps [`arg]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `tactic.generalize [`arg])) [])
         (Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `h [] "←" (Term.doExpr `intro1)))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])
         (Term.doSeqItem
          (Term.doLet
           "let"
           []
           (Term.letDecl
            (Term.letIdDecl
             `locals
             []
             []
             ":="
             (Term.app
              `arg
              [(«term[_]» "[" [] "]")
               (Term.fun
                "fun"
                (Term.basicFun
                 [`e (Term.hole "_") `acc]
                 []
                 "=>"
                 (termIfThenElse "if" `e "then" («term_::_» `e "::" `Acc) "else" `Acc)))]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `locals [(«term_∘_» `try "∘" `clear)])) [])
         (Term.doSeqItem (Term.doExpr (Term.app `pure [`h])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `locals [(«term_∘_» `try "∘" `clear)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» `try "∘" `clear)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `clear
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      `try
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_∘_» `try "∘" `clear) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `locals
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app
       `arg
       [(«term[_]» "[" [] "]")
        (Term.fun
         "fun"
         (Term.basicFun
          [`e (Term.hole "_") `acc]
          []
          "=>"
          (termIfThenElse "if" `e "then" («term_::_» `e "::" `Acc) "else" `Acc)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`e (Term.hole "_") `acc]
        []
        "=>"
        (termIfThenElse "if" `e "then" («term_::_» `e "::" `Acc) "else" `Acc)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse "if" `e "then" («term_::_» `e "::" `Acc) "else" `Acc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Acc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `e "::" `Acc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Acc
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `acc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `intron [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intron
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `intro1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `tactic.generalize [`arg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `arg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.generalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `revert_kdeps [`arg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `arg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `revert_kdeps
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nonlocals
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `tactic.revert [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.revert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `pure
       [(Term.tuple "(" [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`nonlocals])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nonlocals
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» (Term.hole "_") "::" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app
       (Term.proj («term_<|_» `t "<|" (Term.app `env [`n])) "." `partition)
       [(Term.fun "fun" (Term.basicFun [`arg] [(Term.typeSpec ":" `expr)] "=>" `arg))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`arg] [(Term.typeSpec ":" `expr)] "=>" `arg))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `arg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `expr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_<|_» `t "<|" (Term.app `env [`n])) "." `partition)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» `t "<|" (Term.app `env [`n]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `env [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `env
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `t "<|" (Term.app `env [`n]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`locals "," [`nonlocals]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nonlocals
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `locals
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `pure
       [(Term.tuple "(" [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `pure "<|" (Term.app `env [`n]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `env [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `env
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `get_env
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `pure
       [(Term.tuple "(" [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `const [`n (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `whnf_ginductive [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `whnf_ginductive
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `infer_type [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `infer_type
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `pure
       [(Term.tuple "(" [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`e "," [(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`rec_name])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rec_name
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`e "," [`newvars "," `locals]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `locals
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `newvars
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (termIfThenElse
       "if"
       `e
       "then"
       (Term.app `pure [`e])
       "else"
       («term_>>_» (Term.app `tactic.generalize [`e]) ">>" `intro1))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» (Term.app `tactic.generalize [`e]) ">>" `intro1)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `intro1
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `tactic.generalize [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.generalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pure [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `hp)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.tuple "(" [(Term.app `some [`h]) "," [`p]] ")")]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow "let" [] (Term.doIdDecl `x [] "←" (Term.doExpr `get_unused_name)))
              [])
             (Term.doSeqItem
              (Term.doExpr
               (Term.app
                `generalize
                [`h (Term.tuple "(" [] ")") (Term.tuple "(" [`p "," [`x]] ")")]))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `get_local [`x])) [])])))
         (Term.matchAlt
          "|"
          [[(Term.tuple "(" [`none "," [`p]] ")")]]
          "=>"
          (Term.app `i_to_expr [`p]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `i_to_expr [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`none "," [`p]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `x [] "←" (Term.doExpr `get_unused_name)))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app `generalize [`h (Term.tuple "(" [] ")") (Term.tuple "(" [`p "," [`x]] ")")]))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `get_local [`x])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `get_local [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_local
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `generalize [`h (Term.tuple "(" [] ")") (Term.tuple "(" [`p "," [`x]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`p "," [`x]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.tuple "(" [] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `generalize
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `get_unused_name
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.app `some [`h]) "," [`p]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `focus1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `get_main_tag
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
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
       (Init.Meta.Interactive.term_?
        («term_*>_»
         (Term.app `tk [(str "\"generalizing\"")])
         "*>"
         (Init.Meta.Interactive.«term_*» `ident "*"))
        "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_?
       («term_*>_»
        (Term.app `tk [(str "\"generalizing\"")])
        "*>"
        (Init.Meta.Interactive.«term_*» `ident "*"))
       "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      Assuming `x` is a variable in the local context with an inductive type, `induction x` applies induction on `x` to the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor and an inductive hypothesis is added for each recursive argument to the constructor. If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward, so that the inductive hypothesis incorporates that hypothesis as well.
      
      For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `induction n` produces one goal with hypothesis `h : P 0` and target `Q 0`, and one goal with hypotheses `h : P (nat.succ a)` and `ih₁ : P a → Q a` and target `Q (nat.succ a)`. Here the names `a` and `ih₁` ire chosen automatically.
      
      `induction e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then performs induction on the resulting variable.
      
      `induction e with y₁ ... yₙ`, where `e` is a variable or an expression, specifies that the sequence of names `y₁ ... yₙ` should be used for the arguments to the constructors and inductive hypotheses, including implicit arguments. If the list does not include enough names for all of the arguments, additional names are generated automatically. If too many names are given, the extra ones are ignored. Underscores can be used in the list, in which case the corresponding names are generated automatically. Note that for long sequences of names, the `case` tactic provides a more convenient naming mechanism.
      
      `induction e using r` allows the user to specify the principle of induction that should be used. Here `r` should be a theorem whose result type must be of the form `C t`, where `C` is a bound variable and `t` is a (possibly empty) sequence of bound variables
      
      `induction e generalizing z₁ ... zₙ`, where `z₁ ... zₙ` are variables in the local context, generalizes over `z₁ ... zₙ` before applying the induction but then introduces them in each goal. In other words, the net effect is that each inductive hypothesis is generalized.
      
      `induction h : t` will introduce an equality of the form `h : t = C x y`, asserting that the input term is equal to the current constructor case, to the context.
      -/
    unsafe
  def
    induction
    ( hp : parse cases_arg_p )
        ( rec_name : parse using_ident )
        ( ids : parse with_ident_list )
        ( revert : parse <| tk "generalizing" *> ident * ? )
      : tactic Unit
    :=
      do
        let in_tag ← get_main_tag
          focus1
            do
              let
                  e
                    ←
                    match
                      hp
                      with
                      |
                          ( some h , p )
                          =>
                          do let x ← get_unused_name generalize h ( ) ( p , x ) get_local x
                        | ( none , p ) => i_to_expr p
                let e ← if e then pure e else tactic.generalize e >> intro1
                let
                  ( e , newvars , locals )
                    ←
                    do
                      let none ← pure rec_name | pure ( e , [ ] , [ ] )
                        let t ← infer_type e
                        let t ← whnf_ginductive t
                        let const n _ ← pure t | pure ( e , [ ] , [ ] )
                        let env ← get_env
                        let tt ← pure <| env n | pure ( e , [ ] , [ ] )
                        let ( locals , nonlocals ) := t <| env n . partition fun arg : expr => arg
                        let _ :: _ ← pure nonlocals | pure ( e , [ ] , [ ] )
                        let n ← tactic.revert e
                        let
                          newvars
                            ←
                            nonlocals
                              fun
                                arg
                                  =>
                                  do
                                    let n ← revert_kdeps arg
                                      tactic.generalize arg
                                      let h ← intro1
                                      intron n
                                      let
                                        locals := arg [ ] fun e _ acc => if e then e :: Acc else Acc
                                      locals try ∘ clear
                                      pure h
                        intron n - 1
                        let e ← intro1
                        pure ( e , newvars , locals )
                let to_generalize ← revert [ ] . mmap tactic.get_local
                let num_generalized ← revert_lst to_generalize
                let rs ← tactic.induction e ids rec_name
                let
                  gen_hyps
                    ←
                    all_goals
                      do
                        let new_hyps ← intron' num_generalized
                          clear_lst newvars local_pp_name
                          e :: locals . mmap' try ∘ clear
                          pure new_hyps
                set_cases_tags in_tag
                  <|
                  @ List.map₂
                    Name × List expr × List Name × expr
                      _
                      Name × List expr
                      fun ⟨ n , hyps , _ ⟩ gen_hyps => ⟨ n , hyps ++ gen_hyps ⟩
                      rs
                      gen_hyps
#align tactic.interactive.induction tactic.interactive.induction

open CaseTag.MatchResult

private unsafe def goals_with_matching_tag (ns : List Name) :
    tactic (List (expr × case_tag) × List (expr × case_tag)) := do
  let gs ← get_goals
  let (gs : List (expr × tag)) ←
    gs.mmap fun g => do
        let t ← get_tag g
        pure (g, t)
  pure <|
      gs
        (fun ⟨g, t⟩ ⟨exact_matches, suffix_matches⟩ =>
          match case_tag.parse t with
          | none => ⟨exact_matches, suffix_matches⟩
          | some t =>
            match case_tag.match_tag ns t with
            | exact_match => ⟨⟨g, t⟩ :: exact_matches, suffix_matches⟩
            | fuzzy_match => ⟨exact_matches, ⟨g, t⟩ :: suffix_matches⟩
            | no_match => ⟨exact_matches, suffix_matches⟩)
        ([], [])
#align tactic.interactive.goals_with_matching_tag tactic.interactive.goals_with_matching_tag

private unsafe def goal_with_matching_tag (ns : List Name) : tactic (expr × case_tag) := do
  let ⟨exact_matches, suffix_matches⟩ ← goals_with_matching_tag ns
  match exact_matches, suffix_matches with
    | [], [] => fail f! "Invalid `case`: there is no goal tagged with suffix {ns}."
    | [], [g] => pure g
    | [], _ =>
      let tags : List (List Name) := suffix_matches fun ⟨_, t⟩ => t
      fail
        f! "Invalid `case`: there is more than one goal tagged with suffix {ns }.
          Matching tags: {tags}"
    | [g], _ => pure g
    | _, _ => fail f! "Invalid `case`: there is more than one goal tagged with tag {ns}."
#align tactic.interactive.goal_with_matching_tag tactic.interactive.goal_with_matching_tag

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [(Command.unsafe "unsafe")] [])
     (Command.def
      "def"
      (Command.declId `case_arg_parser [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.app
          `lean.parser
          [(«term_×_»
            (Term.app `List [`Name])
            "×"
            (Term.app `Option [(Term.app `List [`Name])]))]))])
      (Command.declValSimple
       ":="
       («term_<*>_»
        («term_<$>_» `Prod.mk "<$>" (Init.Meta.Interactive.«term_*» `ident_ "*"))
        "<*>"
        (Init.Meta.Interactive.term_?
         («term_*>_»
          (Term.app `tk [(str "\":\"")])
          "*>"
          (Init.Meta.Interactive.«term_*» `ident_ "*"))
         "?"))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<*>_»
       («term_<$>_» `Prod.mk "<$>" (Init.Meta.Interactive.«term_*» `ident_ "*"))
       "<*>"
       (Init.Meta.Interactive.term_?
        («term_*>_»
         (Term.app `tk [(str "\":\"")])
         "*>"
         (Init.Meta.Interactive.«term_*» `ident_ "*"))
        "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_?
       («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" (Init.Meta.Interactive.«term_*» `ident_ "*"))
       "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
unsafe
  def
    case_arg_parser
    : lean.parser List Name × Option List Name
    := Prod.mk <$> ident_ * <*> tk ":" *> ident_ * ?
#align tactic.interactive.case_arg_parser tactic.interactive.case_arg_parser

unsafe def case_parser : lean.parser (List (List Name × Option (List Name))) :=
  list_of case_arg_parser <|> Functor.map (fun x => [x]) case_arg_parser
#align tactic.interactive.case_parser tactic.interactive.case_parser

/-
TODO `case` could be generalised to work with zero names as well. The form

  case : x y z { ... }

would select the first goal (or the first goal with a case tag), renaming
hypotheses to `x, y, z`. The renaming functionality would be available only if
the goal has a case tag.
-/
/-- Focuses on a goal ('case') generated by `induction`, `cases` or `with_cases`.

The goal is selected by giving one or more names which must match exactly one
goal. A goal is matched if the given names are a suffix of its goal tag.
Additionally, each name in the sequence can be abbreviated to a suffix of the
corresponding name in the goal tag. Thus, a goal with tag
```
nat.zero, list.nil
```
can be selected with any of these invocations (among others):
```
case nat.zero list.nil {...}
case nat.zero nil      {...}
case zero     nil      {...}
case          nil      {...}
```

Additionally, the form
```
case C : N₀ ... Nₙ {...}
```
can be used to rename hypotheses introduced by the preceding
`cases`/`induction`/`with_cases`, using the names `Nᵢ`. For example:
```
example (xs : list ℕ) : xs = xs :=
begin
  induction xs,
  case nil { reflexivity },
  case cons : x xs ih {
    -- x : ℕ, xs : list ℕ, ih : xs = xs
    reflexivity }
end
```

Note that this renaming functionality only work reliably *directly after* an
`induction`/`cases`/`with_cases`. If you need to perform additional work after
an `induction` or `cases` (e.g. introduce hypotheses in all goals), use
`with_cases`.

Multiple cases can be handled by the same tactic block with
```
case [A : N₀ ... Nₙ, B : M₀ ... Mₙ] {...}
```
-/
unsafe def case (args : parse case_parser) (tac : itactic) : tactic Unit := do
  let target_goals ←
    args.mmap fun ⟨ns, ids⟩ => do
        let ⟨goal, tag⟩ ← goal_with_matching_tag ns
        let ids := ids.getOrElse []
        let num_ids := ids.length
        let goals ← get_goals
        let other_goals := goals.filter (· ≠ goal)
        set_goals [goal]
        match tag with
          | case_tag.pi _ num_args => do
            intro_lst ids
            when (num_ids < num_args) <| intron (num_args - num_ids)
          | case_tag.hyps _ new_hyp_names => do
            let num_new_hyps := new_hyp_names
            when (num_ids > num_new_hyps) <|
                fail
                  f! "Invalid `case`: You gave {num_ids } names, but the case introduces {num_new_hyps} new hypotheses."
            let renamings := native.rb_map.of_list (new_hyp_names ids)
            propagate_tags <| tactic.rename_many renamings tt tt
        let goals ← get_goals
        set_goals other_goals
        match goals with
          | [g] => return g
          | _ => fail "Unexpected goals introduced by renaming"
  let remaining_goals ← get_goals
  set_goals target_goals
  tac
  let unsolved_goals ← get_goals
  match unsolved_goals with
    | [] => set_goals remaining_goals
    | _ => fail "case tactic failed, focused goals have not been solved"
#align tactic.interactive.case tactic.interactive.case

/--
Assuming `x` is a variable in the local context with an inductive type, `destruct x` splits the main goal, producing one goal for each constructor of the inductive type, in which `x` is assumed to be a general instance of that constructor. In contrast to `cases`, the local context is unchanged, i.e. no elements are reverted or introduced.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `destruct n` produces one goal with target `n = 0 → Q n`, and one goal with target `∀ (a : ℕ), (λ (w : ℕ), n = w → Q n) (nat.succ a)`. Here the name `a` is chosen automatically.
-/
unsafe def destruct (p : parse texpr) : tactic Unit :=
  i_to_expr p >>= tactic.destruct
#align tactic.interactive.destruct tactic.interactive.destruct

unsafe def cases_core (e : expr) (ids : List Name := []) : tactic Unit := do
  let in_tag ← get_main_tag
  focus1 do
      let rs ← tactic.cases e ids
      set_cases_tags in_tag rs
#align tactic.interactive.cases_core tactic.interactive.cases_core

/--
Assuming `x` is a variable in the local context with an inductive type, `cases x` splits the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor. If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward, so that the case split affects that hypothesis as well.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `cases n` produces one goal with hypothesis `h : P 0` and target `Q 0`, and one goal with hypothesis `h : P (nat.succ a)` and target `Q (nat.succ a)`. Here the name `a` is chosen automatically.

`cases e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then cases on the resulting variable.

`cases e with y₁ ... yₙ`, where `e` is a variable or an expression, specifies that the sequence of names `y₁ ... yₙ` should be used for the arguments to the constructors, including implicit arguments. If the list does not include enough names for all of the arguments, additional names are generated automatically. If too many names are given, the extra ones are ignored. Underscores can be used in the list, in which case the corresponding names are generated automatically.

`cases h : e`, where `e` is a variable or an expression, performs cases on `e` as above, but also adds a hypothesis `h : e = ...` to each hypothesis, where `...` is the constructor instance for that particular case.
-/
unsafe def cases : parse cases_arg_p → parse with_ident_list → tactic Unit
  | (none, p), ids => do
    let e ← i_to_expr p
    cases_core e ids
  | (some h, p), ids => do
    let x ← get_unused_name
    generalize h () (p, x)
    let hx ← get_local x
    cases_core hx ids
#align tactic.interactive.cases tactic.interactive.cases

private unsafe def find_matching_hyp (ps : List pattern) : tactic expr :=
  any_hyp fun h => do
    let type ← infer_type h
    ps fun p => do
        match_pattern p type
        return h
#align tactic.interactive.find_matching_hyp tactic.interactive.find_matching_hyp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`cases_matching p` applies the `cases` tactic to a hypothesis `h : type` if `type` matches the pattern `p`.\n`cases_matching [p_1, ..., p_n]` applies the `cases` tactic to a hypothesis `h : type` if `type` matches one of the given patterns.\n`cases_matching* p` more efficient and compact version of `focus1 { repeat { cases_matching p } }`. It is more efficient because the pattern is compiled once.\n\nExample: The following tactic destructs all conjunctions and disjunctions in the current goal.\n```\ncases_matching* [_ ∨ _, _ ∧ _]\n```\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `cases_matching [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`rec]
         [":"
          («term_<|_»
           `parse
           "<|"
           (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"*\"")]) "?"))]
         []
         ")")
        (Term.explicitBinder "(" [`ps] [":" (Term.app `parse [`pexpr_list_or_texpr])] [] ")")]
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
             `ps
             []
             "←"
             (Term.doExpr (Term.app (Term.proj `ps "." `mmap) [`pexpr_to_pattern]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (termIfThenElse
             "if"
             `rec
             "then"
             («term_>>=_» (Term.app `find_matching_hyp [`ps]) ">>=" `cases_core)
             "else"
             («term_<|_»
              `tactic.focus1
              "<|"
              («term_<|_»
               `tactic.repeat
               "<|"
               («term_>>=_» (Term.app `find_matching_hyp [`ps]) ">>=" `cases_core)))))
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
            `ps
            []
            "←"
            (Term.doExpr (Term.app (Term.proj `ps "." `mmap) [`pexpr_to_pattern]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (termIfThenElse
            "if"
            `rec
            "then"
            («term_>>=_» (Term.app `find_matching_hyp [`ps]) ">>=" `cases_core)
            "else"
            («term_<|_»
             `tactic.focus1
             "<|"
             («term_<|_»
              `tactic.repeat
              "<|"
              («term_>>=_» (Term.app `find_matching_hyp [`ps]) ">>=" `cases_core)))))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       `rec
       "then"
       («term_>>=_» (Term.app `find_matching_hyp [`ps]) ">>=" `cases_core)
       "else"
       («term_<|_»
        `tactic.focus1
        "<|"
        («term_<|_»
         `tactic.repeat
         "<|"
         («term_>>=_» (Term.app `find_matching_hyp [`ps]) ">>=" `cases_core))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `tactic.focus1
       "<|"
       («term_<|_»
        `tactic.repeat
        "<|"
        («term_>>=_» (Term.app `find_matching_hyp [`ps]) ">>=" `cases_core)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `tactic.repeat
       "<|"
       («term_>>=_» (Term.app `find_matching_hyp [`ps]) ">>=" `cases_core))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>=_» (Term.app `find_matching_hyp [`ps]) ">>=" `cases_core)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cases_core
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `find_matching_hyp [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `find_matching_hyp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 55, (some 56, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `tactic.repeat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `tactic.focus1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>=_» (Term.app `find_matching_hyp [`ps]) ">>=" `cases_core)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cases_core
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `find_matching_hyp [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `find_matching_hyp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 55, (some 56, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app (Term.proj `ps "." `mmap) [`pexpr_to_pattern])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pexpr_to_pattern
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `ps "." `mmap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
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
      (Term.app `parse [`pexpr_list_or_texpr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pexpr_list_or_texpr
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
      («term_<|_» `parse "<|" (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"*\"")]) "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"*\"")]) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      `cases_matching p` applies the `cases` tactic to a hypothesis `h : type` if `type` matches the pattern `p`.
      `cases_matching [p_1, ..., p_n]` applies the `cases` tactic to a hypothesis `h : type` if `type` matches one of the given patterns.
      `cases_matching* p` more efficient and compact version of `focus1 { repeat { cases_matching p } }`. It is more efficient because the pattern is compiled once.
      
      Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
      ```
      cases_matching* [_ ∨ _, _ ∧ _]
      ```
      -/
    unsafe
  def
    cases_matching
    ( rec : parse <| tk "*" ? ) ( ps : parse pexpr_list_or_texpr ) : tactic Unit
    :=
      do
        let ps ← ps . mmap pexpr_to_pattern
          if
            rec
            then
            find_matching_hyp ps >>= cases_core
            else
            tactic.focus1 <| tactic.repeat <| find_matching_hyp ps >>= cases_core
#align tactic.interactive.cases_matching tactic.interactive.cases_matching

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Shorthand for `cases_matching` -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `casesm [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`rec]
         [":"
          («term_<|_»
           `parse
           "<|"
           (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"*\"")]) "?"))]
         []
         ")")
        (Term.explicitBinder "(" [`ps] [":" (Term.app `parse [`pexpr_list_or_texpr])] [] ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple ":=" (Term.app `cases_matching [`rec `ps]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cases_matching [`rec `ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `rec
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cases_matching
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
      (Term.app `parse [`pexpr_list_or_texpr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pexpr_list_or_texpr
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
      («term_<|_» `parse "<|" (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"*\"")]) "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"*\"")]) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
/-- Shorthand for `cases_matching` -/ unsafe
  def
    casesm
    ( rec : parse <| tk "*" ? ) ( ps : parse pexpr_list_or_texpr ) : tactic Unit
    := cases_matching rec ps
#align tactic.interactive.casesm tactic.interactive.casesm

private unsafe def try_cases_for_types (type_names : List Name) (at_most_one : Bool) :
    tactic Unit :=
  any_hyp fun h => do
    let I ← expr.get_app_fn <$> (infer_type h >>= head_beta)
    guard I
    guard (I ∈ type_names)
    tactic.focus1
        (cases_core h >>
          if at_most_one then do
            let n ← num_goals
            guard (n ≤ 1)
          else skip)
#align tactic.interactive.try_cases_for_types tactic.interactive.try_cases_for_types

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`\n`cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis `h : (I_1 ...)` or ... or `h : (I_n ...)`\n`cases_type* I` is shorthand for `focus1 { repeat { cases_type I } }`\n`cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.\n\nExample: The following tactic destructs all conjunctions and disjunctions in the current goal.\n```\ncases_type* or and\n```\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `cases_type [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`one]
         [":"
          («term_<|_»
           `parse
           "<|"
           (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"!\"")]) "?"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`rec]
         [":"
          («term_<|_»
           `parse
           "<|"
           (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"*\"")]) "?"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`type_names]
         [":" (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])]
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
             `type_names
             []
             "←"
             (Term.doExpr (Term.app (Term.proj `type_names "." `mmap) [`resolve_constant]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (termIfThenElse
             "if"
             `rec
             "then"
             (Term.app `try_cases_for_types [`type_names (Term.app `not [`one])])
             "else"
             («term_<|_»
              `tactic.focus1
              "<|"
              («term_<|_»
               `tactic.repeat
               "<|"
               (Term.app `try_cases_for_types [`type_names (Term.app `not [`one])])))))
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
            `type_names
            []
            "←"
            (Term.doExpr (Term.app (Term.proj `type_names "." `mmap) [`resolve_constant]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (termIfThenElse
            "if"
            `rec
            "then"
            (Term.app `try_cases_for_types [`type_names (Term.app `not [`one])])
            "else"
            («term_<|_»
             `tactic.focus1
             "<|"
             («term_<|_»
              `tactic.repeat
              "<|"
              (Term.app `try_cases_for_types [`type_names (Term.app `not [`one])])))))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       `rec
       "then"
       (Term.app `try_cases_for_types [`type_names (Term.app `not [`one])])
       "else"
       («term_<|_»
        `tactic.focus1
        "<|"
        («term_<|_»
         `tactic.repeat
         "<|"
         (Term.app `try_cases_for_types [`type_names (Term.app `not [`one])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `tactic.focus1
       "<|"
       («term_<|_»
        `tactic.repeat
        "<|"
        (Term.app `try_cases_for_types [`type_names (Term.app `not [`one])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `tactic.repeat
       "<|"
       (Term.app `try_cases_for_types [`type_names (Term.app `not [`one])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `try_cases_for_types [`type_names (Term.app `not [`one])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not [`one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `not [`one]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `type_names
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `try_cases_for_types
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `tactic.repeat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `tactic.focus1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `try_cases_for_types [`type_names (Term.app `not [`one])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not [`one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `not [`one]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `type_names
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `try_cases_for_types
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app (Term.proj `type_names "." `mmap) [`resolve_constant])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `resolve_constant
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `type_names "." `mmap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `type_names
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
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
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
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
      `cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
      `cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis `h : (I_1 ...)` or ... or `h : (I_n ...)`
      `cases_type* I` is shorthand for `focus1 { repeat { cases_type I } }`
      `cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.
      
      Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
      ```
      cases_type* or and
      ```
      -/
    unsafe
  def
    cases_type
    ( one : parse <| tk "!" ? ) ( rec : parse <| tk "*" ? ) ( type_names : parse ident * )
      : tactic Unit
    :=
      do
        let type_names ← type_names . mmap resolve_constant
          if
            rec
            then
            try_cases_for_types type_names not one
            else
            tactic.focus1 <| tactic.repeat <| try_cases_for_types type_names not one
#align tactic.interactive.cases_type tactic.interactive.cases_type

/--
Tries to solve the current goal using a canonical proof of `true`, or the `reflexivity` tactic, or the `contradiction` tactic.
-/
unsafe def trivial : tactic Unit :=
  tactic.triv <|> tactic.reflexivity <|> tactic.contradiction <|> fail "trivial tactic failed"
#align tactic.interactive.trivial tactic.interactive.trivial

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Closes the main goal using `sorry`. Takes an optional ignored tactic block.\n\nThe ignored tactic block is useful for \"commenting out\" part of a proof during development:\n```lean\nbegin\n  split,\n  admit { expensive_tactic },\n\nend\n```\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `admit [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`t]
         [":"
          (Term.app
           `parse
           [(Init.Meta.Interactive.term_?
             (Term.app `with_desc [(str "\"{...}\"") `parser.itactic])
             "?")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple ":=" `tactic.admit [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.admit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
       [(Init.Meta.Interactive.term_?
         (Term.app `with_desc [(str "\"{...}\"") `parser.itactic])
         "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? (Term.app `with_desc [(str "\"{...}\"") `parser.itactic]) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      Closes the main goal using `sorry`. Takes an optional ignored tactic block.
      
      The ignored tactic block is useful for "commenting out" part of a proof during development:
      ```lean
      begin
        split,
        admit { expensive_tactic },
      
      end
      ```
      -/
    unsafe
  def admit ( t : parse with_desc "{...}" parser.itactic ? ) : tactic Unit := tactic.admit
#align tactic.interactive.admit tactic.interactive.admit

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Closes the main goal using `sorry`. Takes an optional ignored tactic block.\n\nThe ignored tactic block is useful for \"commenting out\" part of a proof during development:\n```lean\nbegin\n  split,\n  sorry { expensive_tactic },\n\nend\n```\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `sorry [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`t]
         [":"
          (Term.app
           `parse
           [(Init.Meta.Interactive.term_?
             (Term.app `with_desc [(str "\"{...}\"") `parser.itactic])
             "?")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple ":=" `tactic.admit [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.admit
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
       [(Init.Meta.Interactive.term_?
         (Term.app `with_desc [(str "\"{...}\"") `parser.itactic])
         "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? (Term.app `with_desc [(str "\"{...}\"") `parser.itactic]) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      Closes the main goal using `sorry`. Takes an optional ignored tactic block.
      
      The ignored tactic block is useful for "commenting out" part of a proof during development:
      ```lean
      begin
        split,
        sorry { expensive_tactic },
      
      end
      ```
      -/
    unsafe
  def sorry ( t : parse with_desc "{...}" parser.itactic ? ) : tactic Unit := tactic.admit
#align tactic.interactive.sorry tactic.interactive.sorry

/--
The contradiction tactic attempts to find in the current local context a hypothesis that is equivalent to an empty inductive type (e.g. `false`), a hypothesis of the form `c_1 ... = c_2 ...` where `c_1` and `c_2` are distinct constructors, or two contradictory hypotheses.
-/
unsafe def contradiction : tactic Unit :=
  tactic.contradiction
#align tactic.interactive.contradiction tactic.interactive.contradiction

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`iterate { t }` repeatedly applies tactic `t` until `t` fails. `iterate { t }` always succeeds.\n\n`iterate n { t }` applies `t` `n` times.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `iterate [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`n]
         [":" (Term.app `parse [(Init.Meta.Interactive.term_? `small_nat "?")])]
         []
         ")")
        (Term.explicitBinder "(" [`t] [":" `itactic] [] ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `n)]
        "with"
        (Term.matchAlts
         [(Term.matchAlt "|" [[`none]] "=>" (Term.app `tactic.iterate' [`t]))
          (Term.matchAlt "|" [[(Term.app `some [`n])]] "=>" (Term.app `iterate_exactly' [`n `t]))]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `n)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt "|" [[`none]] "=>" (Term.app `tactic.iterate' [`t]))
         (Term.matchAlt "|" [[(Term.app `some [`n])]] "=>" (Term.app `iterate_exactly' [`n `t]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `iterate_exactly' [`n `t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `iterate_exactly'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic.iterate' [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.iterate'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
      `itactic
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [(Init.Meta.Interactive.term_? `small_nat "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? `small_nat "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      `iterate { t }` repeatedly applies tactic `t` until `t` fails. `iterate { t }` always succeeds.
      
      `iterate n { t }` applies `t` `n` times.
      -/
    unsafe
  def
    iterate
    ( n : parse small_nat ? ) ( t : itactic ) : tactic Unit
    := match n with | none => tactic.iterate' t | some n => iterate_exactly' n t
#align tactic.interactive.iterate tactic.interactive.iterate

/-- `repeat { t }` applies `t` to each goal. If the application succeeds,
the tactic is applied recursively to all the generated subgoals until it eventually fails.
The recursion stops in a subgoal when the tactic has failed to make progress.
The tactic `repeat { t }` never fails.
-/
unsafe def repeat : itactic → tactic Unit :=
  tactic.repeat
#align tactic.interactive.repeat tactic.interactive.repeat

/-- `try { t }` tries to apply tactic `t`, but succeeds whether or not `t` succeeds.
-/
unsafe def try : itactic → tactic Unit :=
  tactic.try
#align tactic.interactive.try tactic.interactive.try

/-- A do-nothing tactic that always succeeds.
-/
unsafe def skip : tactic Unit :=
  tactic.skip
#align tactic.interactive.skip tactic.interactive.skip

/-- `solve1 { t }` applies the tactic `t` to the main goal and fails if it is not solved.
-/
unsafe def solve1 : itactic → tactic Unit :=
  tactic.solve1
#align tactic.interactive.solve1 tactic.interactive.solve1

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`abstract id { t }` tries to use tactic `t` to solve the main goal. If it succeeds, it abstracts the goal as an independent definition or theorem with name `id`. If `id` is omitted, a name is generated automatically.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `abstract [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`id]
         [":" (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])]
         []
         ")")
        (Term.explicitBinder "(" [`tac] [":" `itactic] [] ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple ":=" (Term.app `tactic.abstract [`tac `id]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.abstract [`tac `id])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `id
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `tac
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.abstract
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
      `itactic
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? `ident "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      `abstract id { t }` tries to use tactic `t` to solve the main goal. If it succeeds, it abstracts the goal as an independent definition or theorem with name `id`. If `id` is omitted, a name is generated automatically.
      -/
    unsafe
  def abstract ( id : parse ident ? ) ( tac : itactic ) : tactic Unit := tactic.abstract tac id
#align tactic.interactive.abstract tactic.interactive.abstract

/--
`all_goals { t }` applies the tactic `t` to every goal, and succeeds if each application succeeds.
-/
unsafe def all_goals : itactic → tactic Unit :=
  tactic.all_goals'
#align tactic.interactive.all_goals tactic.interactive.all_goals

/--
`any_goals { t }` applies the tactic `t` to every goal, and succeeds if at least one application succeeds.
-/
unsafe def any_goals : itactic → tactic Unit :=
  tactic.any_goals'
#align tactic.interactive.any_goals tactic.interactive.any_goals

/--
`focus { t }` temporarily hides all goals other than the first, applies `t`, and then restores the other goals. It fails if there are no goals.
-/
unsafe def focus (tac : itactic) : tactic Unit :=
  tactic.focus1 tac
#align tactic.interactive.focus tactic.interactive.focus

private unsafe def assume_core (n : Name) (ty : pexpr) := do
  let t ← target
  when (Not <| t ∨ t) whnf_target
  let t ← target
  when (Not <| t ∨ t) <| fail "assume tactic failed, Pi/let expression expected"
  let ty ← i_to_expr ``(($(ty) : Sort _))
  unify ty t
  intro_core n >> skip
#align tactic.interactive.assume_core tactic.interactive.assume_core

/--
Assuming the target of the goal is a Pi or a let, `assume h : t` unifies the type of the binder with `t` and introduces it with name `h`, just like `intro h`. If `h` is absent, the tactic uses the name `this`. If `t` is omitted, it will be inferred.

`assume (h₁ : t₁) ... (hₙ : tₙ)` introduces multiple hypotheses. Any of the types may be omitted, but the names must be present.
-/
unsafe def assume :
    parse (Sum.inl <$> (tk ":" *> texpr) <|> Sum.inr <$> parse_binders tac_rbp) → tactic Unit
  | Sum.inl ty => assume_core `this ty
  | Sum.inr binders => binders.mmap' fun b => assume_core b.local_pp_name b.local_type
#align tactic.interactive.assume tactic.interactive.assume

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`have h : t := p` adds the hypothesis `h : t` to the current goal if `p` a term of type `t`. If `t` is omitted, it will be inferred.\n\n`have h : t` adds the hypothesis `h : t` to the current goal and opens a new subgoal with target `t`. The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh metavariable.\n\nIf `h` is omitted, the name `this` is used.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `have [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`q₁]
         [":"
          (Term.app
           `parse
           [(Init.Meta.Interactive.term_?
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
           (Init.Meta.Interactive.term_?
            («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
            "?"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
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
                  (Term.doIdDecl
                   `t
                   []
                   "←"
                   (Term.doExpr
                    (Term.app
                     `i_to_expr
                     [(Term.precheckedQuot
                       "`"
                       (Term.quot
                        "`("
                        (Term.typeAscription
                         "("
                         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                         ":"
                         [(Term.sort "Sort" [(Level.hole "_")])]
                         ")")
                        ")"))]))))
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
                     `i_to_expr
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
                (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`h `t `v])) [])])))
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
                  (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `tactic.note [`h `none `p])) [])])))
            (Term.matchAlt
             "|"
             [[(Term.app `some [`e]) "," `none]]
             "=>"
             («term_>>=_»
              (Term.app
               `i_to_expr
               [(Term.precheckedQuot
                 "`"
                 (Term.quot
                  "`("
                  (Term.typeAscription
                   "("
                   (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                   ":"
                   [(Term.sort "Sort" [(Level.hole "_")])]
                   ")")
                  ")"))])
              ">>="
              (Term.app `tactic.assert [`h])))
            (Term.matchAlt
             "|"
             [[`none "," `none]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `e
                   []
                   "←"
                   (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `tactic.assert [`h `e])) [])])))]))
         ">>"
         `skip))
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
                 (Term.doIdDecl
                  `t
                  []
                  "←"
                  (Term.doExpr
                   (Term.app
                    `i_to_expr
                    [(Term.precheckedQuot
                      "`"
                      (Term.quot
                       "`("
                       (Term.typeAscription
                        "("
                        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                        ":"
                        [(Term.sort "Sort" [(Level.hole "_")])]
                        ")")
                       ")"))]))))
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
                    `i_to_expr
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
               (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`h `t `v])) [])])))
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
                 (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `tactic.note [`h `none `p])) [])])))
           (Term.matchAlt
            "|"
            [[(Term.app `some [`e]) "," `none]]
            "=>"
            («term_>>=_»
             (Term.app
              `i_to_expr
              [(Term.precheckedQuot
                "`"
                (Term.quot
                 "`("
                 (Term.typeAscription
                  "("
                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                  ":"
                  [(Term.sort "Sort" [(Level.hole "_")])]
                  ")")
                 ")"))])
             ">>="
             (Term.app `tactic.assert [`h])))
           (Term.matchAlt
            "|"
            [[`none "," `none]]
            "=>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
                [])
               (Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl
                  `e
                  []
                  "←"
                  (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `tactic.assert [`h `e])) [])])))]))
        ">>"
        `skip))
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
                (Term.doIdDecl
                 `t
                 []
                 "←"
                 (Term.doExpr
                  (Term.app
                   `i_to_expr
                   [(Term.precheckedQuot
                     "`"
                     (Term.quot
                      "`("
                      (Term.typeAscription
                       "("
                       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                       ":"
                       [(Term.sort "Sort" [(Level.hole "_")])]
                       ")")
                      ")"))]))))
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
                   `i_to_expr
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
              (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`h `t `v])) [])])))
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
                (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `tactic.note [`h `none `p])) [])])))
          (Term.matchAlt
           "|"
           [[(Term.app `some [`e]) "," `none]]
           "=>"
           («term_>>=_»
            (Term.app
             `i_to_expr
             [(Term.precheckedQuot
               "`"
               (Term.quot
                "`("
                (Term.typeAscription
                 "("
                 (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                 ":"
                 [(Term.sort "Sort" [(Level.hole "_")])]
                 ")")
                ")"))])
            ">>="
            (Term.app `tactic.assert [`h])))
          (Term.matchAlt
           "|"
           [[`none "," `none]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl
                 `e
                 []
                 "←"
                 (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `tactic.assert [`h `e])) [])])))]))
       ">>"
       `skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
               (Term.doIdDecl
                `t
                []
                "←"
                (Term.doExpr
                 (Term.app
                  `i_to_expr
                  [(Term.precheckedQuot
                    "`"
                    (Term.quot
                     "`("
                     (Term.typeAscription
                      "("
                      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                      ":"
                      [(Term.sort "Sort" [(Level.hole "_")])]
                      ")")
                     ")"))]))))
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
                  `i_to_expr
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
             (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`h `t `v])) [])])))
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
               (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `tactic.note [`h `none `p])) [])])))
         (Term.matchAlt
          "|"
          [[(Term.app `some [`e]) "," `none]]
          "=>"
          («term_>>=_»
           (Term.app
            `i_to_expr
            [(Term.precheckedQuot
              "`"
              (Term.quot
               "`("
               (Term.typeAscription
                "("
                (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                ":"
                [(Term.sort "Sort" [(Level.hole "_")])]
                ")")
               ")"))])
           ">>="
           (Term.app `tactic.assert [`h])))
         (Term.matchAlt
          "|"
          [[`none "," `none]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl
                `e
                []
                "←"
                (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `tactic.assert [`h `e])) [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `tactic.assert [`h `e])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.assert [`h `e])
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
      `tactic.assert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `mk_meta_var [(Term.app `sort [`u])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sort [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sort
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `sort [`u]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk_meta_var
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `mk_meta_univ
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
      («term_>>=_»
       (Term.app
        `i_to_expr
        [(Term.precheckedQuot
          "`"
          (Term.quot
           "`("
           (Term.typeAscription
            "("
            (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
            ":"
            [(Term.sort "Sort" [(Level.hole "_")])]
            ")")
           ")"))])
       ">>="
       (Term.app `tactic.assert [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.assert [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.assert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app
       `i_to_expr
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.typeAscription
           "("
           (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
           ":"
           [(Term.sort "Sort" [(Level.hole "_")])]
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
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
         ":"
         [(Term.sort "Sort" [(Level.hole "_")])]
         ")")
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
       ":"
       [(Term.sort "Sort" [(Level.hole "_")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.sort "Sort" [(Level.hole "_")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Level.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024,
     level) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
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
           (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `tactic.note [`h `none `p])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.note [`h `none `p])
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
      `tactic.note
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `i_to_expr [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
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
           (Term.doIdDecl
            `t
            []
            "←"
            (Term.doExpr
             (Term.app
              `i_to_expr
              [(Term.precheckedQuot
                "`"
                (Term.quot
                 "`("
                 (Term.typeAscription
                  "("
                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                  ":"
                  [(Term.sort "Sort" [(Level.hole "_")])]
                  ")")
                 ")"))]))))
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
              `i_to_expr
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
         (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`h `t `v])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.assertv [`h `t `v])
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
      `tactic.assertv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `i_to_expr
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
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `i_to_expr
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.typeAscription
           "("
           (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
           ":"
           [(Term.sort "Sort" [(Level.hole "_")])]
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
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
         ":"
         [(Term.sort "Sort" [(Level.hole "_")])]
         ")")
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
       ":"
       [(Term.sort "Sort" [(Level.hole "_")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.sort "Sort" [(Level.hole "_")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Level.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024,
     level) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
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
              (Term.doIdDecl
               `t
               []
               "←"
               (Term.doExpr
                (Term.app
                 `i_to_expr
                 [(Term.precheckedQuot
                   "`"
                   (Term.quot
                    "`("
                    (Term.typeAscription
                     "("
                     (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                     ":"
                     [(Term.sort "Sort" [(Level.hole "_")])]
                     ")")
                    ")"))]))))
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
                 `i_to_expr
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
            (Term.doSeqItem (Term.doExpr (Term.app `tactic.assertv [`h `t `v])) [])])))
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
              (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `tactic.note [`h `none `p])) [])])))
        (Term.matchAlt
         "|"
         [[(Term.app `some [`e]) "," `none]]
         "=>"
         («term_>>=_»
          (Term.app
           `i_to_expr
           [(Term.precheckedQuot
             "`"
             (Term.quot
              "`("
              (Term.typeAscription
               "("
               (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
               ":"
               [(Term.sort "Sort" [(Level.hole "_")])]
               ")")
              ")"))])
          ">>="
          (Term.app `tactic.assert [`h])))
        (Term.matchAlt
         "|"
         [[`none "," `none]]
         "=>"
         (Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
             [])
            (Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl
               `e
               []
               "←"
               (Term.doExpr (Term.app `mk_meta_var [(Term.paren "(" (Term.app `sort [`u]) ")")]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `tactic.assert [`h `e])) [])])))]))
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
       (Init.Meta.Interactive.term_? («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr) "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      `have h : t := p` adds the hypothesis `h : t` to the current goal if `p` a term of type `t`. If `t` is omitted, it will be inferred.
      
      `have h : t` adds the hypothesis `h : t` to the current goal and opens a new subgoal with target `t`. The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh metavariable.
      
      If `h` is omitted, the name `this` is used.
      -/
    unsafe
  def
    have
    ( h : parse ident ? ) ( q₁ : parse tk ":" *> texpr ? ) ( q₂ : parse <| tk ":=" *> texpr ? )
      : tactic Unit
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
                  let t ← i_to_expr ` `( ( $ ( e ) : Sort _ ) )
                    let v ← i_to_expr ` `( ( $ ( p ) : $ ( t ) ) )
                    tactic.assertv h t v
              | none , some p => do let p ← i_to_expr p tactic.note h none p
              | some e , none => i_to_expr ` `( ( $ ( e ) : Sort _ ) ) >>= tactic.assert h
              | none , none => do let u ← mk_meta_univ let e ← mk_meta_var sort u tactic.assert h e
          >>
          skip
#align tactic.interactive.have tactic.interactive.have

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`let h : t := p` adds the hypothesis `h : t := p` to the current goal if `p` a term of type `t`. If `t` is omitted, it will be inferred.\n\n`let h : t` adds the hypothesis `h : t := ?M` to the current goal and opens a new subgoal `?M : t`. The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh metavariable.\n\nIf `h` is omitted, the name `this` is used.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `let [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`q₁]
         [":"
          (Term.app
           `parse
           [(Init.Meta.Interactive.term_?
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
           (Init.Meta.Interactive.term_?
            («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
            "?"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
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
                  (Term.doIdDecl
                   `t
                   []
                   "←"
                   (Term.doExpr
                    (Term.app
                     `i_to_expr
                     [(Term.precheckedQuot
                       "`"
                       (Term.quot
                        "`("
                        (Term.typeAscription
                         "("
                         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                         ":"
                         [(Term.sort "Sort" [(Level.hole "_")])]
                         ")")
                        ")"))]))))
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
                     `i_to_expr
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
                (Term.doSeqItem (Term.doExpr (Term.app `tactic.definev [`h `t `v])) [])])))
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
                  (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `tactic.pose [`h `none `p])) [])])))
            (Term.matchAlt
             "|"
             [[(Term.app `some [`e]) "," `none]]
             "=>"
             («term_>>=_»
              (Term.app
               `i_to_expr
               [(Term.precheckedQuot
                 "`"
                 (Term.quot
                  "`("
                  (Term.typeAscription
                   "("
                   (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                   ":"
                   [(Term.sort "Sort" [(Level.hole "_")])]
                   ")")
                  ")"))])
              ">>="
              (Term.app `tactic.define [`h])))
            (Term.matchAlt
             "|"
             [[`none "," `none]]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `e
                   []
                   "←"
                   (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
                 [])
                (Term.doSeqItem (Term.doExpr (Term.app `tactic.define [`h `e])) [])])))]))
         ">>"
         `skip))
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
                 (Term.doIdDecl
                  `t
                  []
                  "←"
                  (Term.doExpr
                   (Term.app
                    `i_to_expr
                    [(Term.precheckedQuot
                      "`"
                      (Term.quot
                       "`("
                       (Term.typeAscription
                        "("
                        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                        ":"
                        [(Term.sort "Sort" [(Level.hole "_")])]
                        ")")
                       ")"))]))))
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
                    `i_to_expr
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
               (Term.doSeqItem (Term.doExpr (Term.app `tactic.definev [`h `t `v])) [])])))
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
                 (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `tactic.pose [`h `none `p])) [])])))
           (Term.matchAlt
            "|"
            [[(Term.app `some [`e]) "," `none]]
            "=>"
            («term_>>=_»
             (Term.app
              `i_to_expr
              [(Term.precheckedQuot
                "`"
                (Term.quot
                 "`("
                 (Term.typeAscription
                  "("
                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                  ":"
                  [(Term.sort "Sort" [(Level.hole "_")])]
                  ")")
                 ")"))])
             ">>="
             (Term.app `tactic.define [`h])))
           (Term.matchAlt
            "|"
            [[`none "," `none]]
            "=>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
                [])
               (Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl
                  `e
                  []
                  "←"
                  (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
                [])
               (Term.doSeqItem (Term.doExpr (Term.app `tactic.define [`h `e])) [])])))]))
        ">>"
        `skip))
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
                (Term.doIdDecl
                 `t
                 []
                 "←"
                 (Term.doExpr
                  (Term.app
                   `i_to_expr
                   [(Term.precheckedQuot
                     "`"
                     (Term.quot
                      "`("
                      (Term.typeAscription
                       "("
                       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                       ":"
                       [(Term.sort "Sort" [(Level.hole "_")])]
                       ")")
                      ")"))]))))
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
                   `i_to_expr
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
              (Term.doSeqItem (Term.doExpr (Term.app `tactic.definev [`h `t `v])) [])])))
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
                (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `tactic.pose [`h `none `p])) [])])))
          (Term.matchAlt
           "|"
           [[(Term.app `some [`e]) "," `none]]
           "=>"
           («term_>>=_»
            (Term.app
             `i_to_expr
             [(Term.precheckedQuot
               "`"
               (Term.quot
                "`("
                (Term.typeAscription
                 "("
                 (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                 ":"
                 [(Term.sort "Sort" [(Level.hole "_")])]
                 ")")
                ")"))])
            ">>="
            (Term.app `tactic.define [`h])))
          (Term.matchAlt
           "|"
           [[`none "," `none]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl
                 `e
                 []
                 "←"
                 (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `tactic.define [`h `e])) [])])))]))
       ">>"
       `skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
               (Term.doIdDecl
                `t
                []
                "←"
                (Term.doExpr
                 (Term.app
                  `i_to_expr
                  [(Term.precheckedQuot
                    "`"
                    (Term.quot
                     "`("
                     (Term.typeAscription
                      "("
                      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                      ":"
                      [(Term.sort "Sort" [(Level.hole "_")])]
                      ")")
                     ")"))]))))
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
                  `i_to_expr
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
             (Term.doSeqItem (Term.doExpr (Term.app `tactic.definev [`h `t `v])) [])])))
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
               (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `tactic.pose [`h `none `p])) [])])))
         (Term.matchAlt
          "|"
          [[(Term.app `some [`e]) "," `none]]
          "=>"
          («term_>>=_»
           (Term.app
            `i_to_expr
            [(Term.precheckedQuot
              "`"
              (Term.quot
               "`("
               (Term.typeAscription
                "("
                (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                ":"
                [(Term.sort "Sort" [(Level.hole "_")])]
                ")")
               ")"))])
           ">>="
           (Term.app `tactic.define [`h])))
         (Term.matchAlt
          "|"
          [[`none "," `none]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl
                `e
                []
                "←"
                (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `tactic.define [`h `e])) [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `e [] "←" (Term.doExpr (Term.app `mk_meta_var [(Term.app `sort [`u])]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `tactic.define [`h `e])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.define [`h `e])
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
      `tactic.define
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `mk_meta_var [(Term.app `sort [`u])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sort [`u])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sort
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `sort [`u]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk_meta_var
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `mk_meta_univ
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
      («term_>>=_»
       (Term.app
        `i_to_expr
        [(Term.precheckedQuot
          "`"
          (Term.quot
           "`("
           (Term.typeAscription
            "("
            (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
            ":"
            [(Term.sort "Sort" [(Level.hole "_")])]
            ")")
           ")"))])
       ">>="
       (Term.app `tactic.define [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.define [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.define
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app
       `i_to_expr
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.typeAscription
           "("
           (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
           ":"
           [(Term.sort "Sort" [(Level.hole "_")])]
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
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
         ":"
         [(Term.sort "Sort" [(Level.hole "_")])]
         ")")
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
       ":"
       [(Term.sort "Sort" [(Level.hole "_")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.sort "Sort" [(Level.hole "_")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Level.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024,
     level) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
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
           (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `tactic.pose [`h `none `p])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.pose [`h `none `p])
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
      `tactic.pose
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `i_to_expr [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
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
           (Term.doIdDecl
            `t
            []
            "←"
            (Term.doExpr
             (Term.app
              `i_to_expr
              [(Term.precheckedQuot
                "`"
                (Term.quot
                 "`("
                 (Term.typeAscription
                  "("
                  (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                  ":"
                  [(Term.sort "Sort" [(Level.hole "_")])]
                  ")")
                 ")"))]))))
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
              `i_to_expr
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
         (Term.doSeqItem (Term.doExpr (Term.app `tactic.definev [`h `t `v])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.definev [`h `t `v])
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
      `tactic.definev
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `i_to_expr
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
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `i_to_expr
       [(Term.precheckedQuot
         "`"
         (Term.quot
          "`("
          (Term.typeAscription
           "("
           (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
           ":"
           [(Term.sort "Sort" [(Level.hole "_")])]
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
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
         ":"
         [(Term.sort "Sort" [(Level.hole "_")])]
         ")")
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
       ":"
       [(Term.sort "Sort" [(Level.hole "_")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.sort "Sort" [(Level.hole "_")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Level.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024,
     level) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
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
              (Term.doIdDecl
               `t
               []
               "←"
               (Term.doExpr
                (Term.app
                 `i_to_expr
                 [(Term.precheckedQuot
                   "`"
                   (Term.quot
                    "`("
                    (Term.typeAscription
                     "("
                     (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                     ":"
                     [(Term.sort "Sort" [(Level.hole "_")])]
                     ")")
                    ")"))]))))
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
                 `i_to_expr
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
            (Term.doSeqItem (Term.doExpr (Term.app `tactic.definev [`h `t `v])) [])])))
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
              (Term.doIdDecl `p [] "←" (Term.doExpr (Term.app `i_to_expr [`p]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `tactic.pose [`h `none `p])) [])])))
        (Term.matchAlt
         "|"
         [[(Term.app `some [`e]) "," `none]]
         "=>"
         («term_>>=_»
          (Term.app
           `i_to_expr
           [(Term.precheckedQuot
             "`"
             (Term.quot
              "`("
              (Term.typeAscription
               "("
               (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
               ":"
               [(Term.sort "Sort" [(Level.hole "_")])]
               ")")
              ")"))])
          ">>="
          (Term.app `tactic.define [`h])))
        (Term.matchAlt
         "|"
         [[`none "," `none]]
         "=>"
         (Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow "let" [] (Term.doIdDecl `u [] "←" (Term.doExpr `mk_meta_univ)))
             [])
            (Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl
               `e
               []
               "←"
               (Term.doExpr (Term.app `mk_meta_var [(Term.paren "(" (Term.app `sort [`u]) ")")]))))
             [])
            (Term.doSeqItem (Term.doExpr (Term.app `tactic.define [`h `e])) [])])))]))
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
       (Init.Meta.Interactive.term_? («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr) "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      `let h : t := p` adds the hypothesis `h : t := p` to the current goal if `p` a term of type `t`. If `t` is omitted, it will be inferred.
      
      `let h : t` adds the hypothesis `h : t := ?M` to the current goal and opens a new subgoal `?M : t`. The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh metavariable.
      
      If `h` is omitted, the name `this` is used.
      -/
    unsafe
  def
    let
    ( h : parse ident ? ) ( q₁ : parse tk ":" *> texpr ? ) ( q₂ : parse <| tk ":=" *> texpr ? )
      : tactic Unit
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
                  let t ← i_to_expr ` `( ( $ ( e ) : Sort _ ) )
                    let v ← i_to_expr ` `( ( $ ( p ) : $ ( t ) ) )
                    tactic.definev h t v
              | none , some p => do let p ← i_to_expr p tactic.pose h none p
              | some e , none => i_to_expr ` `( ( $ ( e ) : Sort _ ) ) >>= tactic.define h
              | none , none => do let u ← mk_meta_univ let e ← mk_meta_var sort u tactic.define h e
          >>
          skip
#align tactic.interactive.let tactic.interactive.let

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`suffices h : t` is the same as `have h : t, tactic.swap`. In other words, it adds the hypothesis `h : t` to the current goal and opens a new subgoal with target `t`.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `suffices [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`h]
         [":" (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`t]
         [":"
          (Term.app
           `parse
           [(Init.Meta.Interactive.term_?
             («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `texpr)
             "?")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple ":=" («term_>>_» (Term.app `have [`h `t `none]) ">>" `tactic.swap) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» (Term.app `have [`h `t `none]) ">>" `tactic.swap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.swap
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `have [`h `t `none])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
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
      `have
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
      (Term.app
       `parse
       [(Init.Meta.Interactive.term_? («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `texpr) "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `texpr) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      `suffices h : t` is the same as `have h : t, tactic.swap`. In other words, it adds the hypothesis `h : t` to the current goal and opens a new subgoal with target `t`.
      -/
    unsafe
  def
    suffices
    ( h : parse ident ? ) ( t : parse tk ":" *> texpr ? ) : tactic Unit
    := have h t none >> tactic.swap
#align tactic.interactive.suffices tactic.interactive.suffices

/-- This tactic displays the current state in the tracing buffer.
-/
unsafe def trace_state : tactic Unit :=
  tactic.trace_state
#align tactic.interactive.trace_state tactic.interactive.trace_state

/-- `trace a` displays `a` in the tracing buffer.
-/
unsafe def trace {α : Type} [has_to_tactic_format α] (a : α) : tactic Unit :=
  tactic.trace a
#align tactic.interactive.trace tactic.interactive.trace

/--
`existsi e` will instantiate an existential quantifier in the target with `e` and leave the instantiated body as the new target. More generally, it applies to any inductive type with one constructor and at least two arguments, applying the constructor with `e` as the first argument and leaving the remaining arguments as goals.

`existsi [e₁, ..., eₙ]` iteratively does the same for each expression in the list.
-/
unsafe def existsi : parse pexpr_list_or_texpr → tactic Unit
  | [] => return ()
  | p :: ps => (i_to_expr p >>= tactic.existsi) >> existsi ps
#align tactic.interactive.existsi tactic.interactive.existsi

/--
This tactic applies to a goal such that its conclusion is an inductive type (say `I`). It tries to apply each constructor of `I` until it succeeds.
-/
unsafe def constructor : tactic Unit :=
  concat_tags tactic.constructor
#align tactic.interactive.constructor tactic.interactive.constructor

/-- Similar to `constructor`, but only non-dependent premises are added as new goals.
-/
unsafe def econstructor : tactic Unit :=
  concat_tags tactic.econstructor
#align tactic.interactive.econstructor tactic.interactive.econstructor

/--
Applies the first constructor when the type of the target is an inductive data type with two constructors.
-/
unsafe def left : tactic Unit :=
  concat_tags tactic.left
#align tactic.interactive.left tactic.interactive.left

/--
Applies the second constructor when the type of the target is an inductive data type with two constructors.
-/
unsafe def right : tactic Unit :=
  concat_tags tactic.right
#align tactic.interactive.right tactic.interactive.right

/--
Applies the constructor when the type of the target is an inductive data type with one constructor.
-/
unsafe def split : tactic Unit :=
  concat_tags tactic.split
#align tactic.interactive.split tactic.interactive.split

private unsafe def constructor_matching_aux (ps : List pattern) : tactic Unit := do
  let t ← target
  ps fun p => match_pattern p t
  constructor
#align tactic.interactive.constructor_matching_aux tactic.interactive.constructor_matching_aux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [(Command.unsafe "unsafe")] [])
     (Command.def
      "def"
      (Command.declId `constructor_matching [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`rec]
         [":"
          («term_<|_»
           `parse
           "<|"
           (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"*\"")]) "?"))]
         []
         ")")
        (Term.explicitBinder "(" [`ps] [":" (Term.app `parse [`pexpr_list_or_texpr])] [] ")")]
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
             `ps
             []
             "←"
             (Term.doExpr (Term.app (Term.proj `ps "." `mmap) [`pexpr_to_pattern]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (termIfThenElse
             "if"
             `rec
             "then"
             (Term.app `constructor_matching_aux [`ps])
             "else"
             («term_<|_»
              `tactic.focus1
              "<|"
              («term_<|_» `tactic.repeat "<|" (Term.app `constructor_matching_aux [`ps])))))
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
            `ps
            []
            "←"
            (Term.doExpr (Term.app (Term.proj `ps "." `mmap) [`pexpr_to_pattern]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (termIfThenElse
            "if"
            `rec
            "then"
            (Term.app `constructor_matching_aux [`ps])
            "else"
            («term_<|_»
             `tactic.focus1
             "<|"
             («term_<|_» `tactic.repeat "<|" (Term.app `constructor_matching_aux [`ps])))))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       `rec
       "then"
       (Term.app `constructor_matching_aux [`ps])
       "else"
       («term_<|_»
        `tactic.focus1
        "<|"
        («term_<|_» `tactic.repeat "<|" (Term.app `constructor_matching_aux [`ps]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `tactic.focus1
       "<|"
       («term_<|_» `tactic.repeat "<|" (Term.app `constructor_matching_aux [`ps])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `tactic.repeat "<|" (Term.app `constructor_matching_aux [`ps]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `constructor_matching_aux [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `constructor_matching_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `tactic.repeat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `tactic.focus1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `constructor_matching_aux [`ps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `constructor_matching_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app (Term.proj `ps "." `mmap) [`pexpr_to_pattern])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pexpr_to_pattern
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `ps "." `mmap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ps
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
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
      (Term.app `parse [`pexpr_list_or_texpr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pexpr_list_or_texpr
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
      («term_<|_» `parse "<|" (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"*\"")]) "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"*\"")]) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
    constructor_matching
    ( rec : parse <| tk "*" ? ) ( ps : parse pexpr_list_or_texpr ) : tactic Unit
    :=
      do
        let ps ← ps . mmap pexpr_to_pattern
          if
            rec
            then
            constructor_matching_aux ps
            else
            tactic.focus1 <| tactic.repeat <| constructor_matching_aux ps
#align tactic.interactive.constructor_matching tactic.interactive.constructor_matching

/-- Replaces the target of the main goal by `false`.
-/
unsafe def exfalso : tactic Unit :=
  tactic.exfalso
#align tactic.interactive.exfalso tactic.interactive.exfalso

/--
The `injection` tactic is based on the fact that constructors of inductive data types are injections. That means that if `c` is a constructor of an inductive datatype, and if `(c t₁)` and `(c t₂)` are two terms that are equal then  `t₁` and `t₂` are equal too.

If `q` is a proof of a statement of conclusion `t₁ = t₂`, then injection applies injectivity to derive the equality of all arguments of `t₁` and `t₂` placed in the same positions. For example, from `(a::b) = (c::d)` we derive `a=c` and `b=d`. To use this tactic `t₁` and `t₂` should be constructor applications of the same constructor.

Given `h : a::b = c::d`, the tactic `injection h` adds two new hypothesis with types `a = c` and `b = d` to the main goal. The tactic `injection h with h₁ h₂` uses the names `h₁` and `h₂` to name the new hypotheses.
-/
unsafe def injection (q : parse texpr) (hs : parse with_ident_list) : tactic Unit := do
  let e ← i_to_expr q
  tactic.injection_with e hs
  try assumption
#align tactic.interactive.injection tactic.interactive.injection

/--
`injections with h₁ ... hₙ` iteratively applies `injection` to hypotheses using the names `h₁ ... hₙ`.
-/
unsafe def injections (hs : parse with_ident_list) : tactic Unit := do
  tactic.injections_with hs
  try assumption
#align tactic.interactive.injections tactic.interactive.injections

end Interactive

unsafe structure simp_config_ext extends SimpConfig where
  discharger : tactic Unit := failed
#align tactic.simp_config_ext tactic.simp_config_ext

section MkSimpSet

open Expr Interactive.Types

unsafe inductive simp_arg_type : Type
  | all_hyps : simp_arg_type
  | except : Name → simp_arg_type
  | expr : pexpr → simp_arg_type
  | symm_expr : pexpr → simp_arg_type
  deriving has_reflect
#align tactic.simp_arg_type tactic.simp_arg_type

unsafe instance simp_arg_type_to_tactic_format : has_to_tactic_format simp_arg_type :=
  ⟨fun a =>
    match a with
    | simp_arg_type.all_hyps => pure "*"
    | simp_arg_type.except n => pure f! "-{n}"
    | simp_arg_type.expr e => i_to_expr_no_subgoals e >>= pp
    | simp_arg_type.symm_expr e => (· ++ ·) "←" <$> (i_to_expr_no_subgoals e >>= pp)⟩
#align tactic.simp_arg_type_to_tactic_format tactic.simp_arg_type_to_tactic_format

unsafe def simp_arg : parser simp_arg_type :=
  tk "*" *> return simp_arg_type.all_hyps <|>
    tk "-" *> simp_arg_type.except <$> ident <|>
      tk "<-" *> simp_arg_type.symm_expr <$> texpr <|> simp_arg_type.expr <$> texpr
#align tactic.simp_arg tactic.simp_arg

unsafe def simp_arg_list : parser (List simp_arg_type) :=
  tk "*" *> return [simp_arg_type.all_hyps] <|> list_of simp_arg <|> return []
#align tactic.simp_arg_list tactic.simp_arg_list

private unsafe def resolve_exception_ids (all_hyps : Bool) :
    List Name → List Name → List Name → tactic (List Name × List Name)
  | [], gex, hex => return (gex.reverse, hex.reverse)
  | id :: ids, gex, hex => do
    let p ← resolve_name id
    let e := p.erase_annotations.get_app_fn.erase_annotations
    match e with
      | const n _ => resolve_exception_ids ids (n :: gex) hex
      | local_const n _ _ _ =>
        when (Not all_hyps) (fail <| s! "invalid local exception {id}, '*' was not used") >>
          resolve_exception_ids ids gex (n :: hex)
      | _ => fail <| s! "invalid exception {id}, unknown identifier"
#align tactic.resolve_exception_ids tactic.resolve_exception_ids

/-- Decode a list of `simp_arg_type` into lists for each type.

  This is a backwards-compatibility version of `decode_simp_arg_list_with_symm`.
  This version fails when an argument of the form `simp_arg_type.symm_expr`
  is included, so that `simp`-like tactics that do not (yet) support backwards rewriting
  should properly report an error but function normally on other inputs.
-/
unsafe def decode_simp_arg_list (hs : List simp_arg_type) :
    tactic <| List pexpr × List Name × List Name × Bool := do
  let (hs, ex, all) ←
    hs.mfoldl
        (fun (r : List pexpr × List Name × Bool) h => do
          let (es, ex, all) := r
          match h with
            | simp_arg_type.all_hyps => pure (es, ex, tt)
            | simp_arg_type.except id => pure (es, id :: ex, all)
            | simp_arg_type.expr e => pure (e :: es, ex, all)
            | simp_arg_type.symm_expr _ => fail "arguments of the form '←...' are not supported")
        ([], [], false)
  let (gex, hex) ← resolve_exception_ids all ex [] []
  return (hs, gex, hex, all)
#align tactic.decode_simp_arg_list tactic.decode_simp_arg_list

/-- Decode a list of `simp_arg_type` into lists for each type.

  This is the newer version of `decode_simp_arg_list`,
  and has a new name for backwards compatibility.
  This version indicates the direction of a `simp` lemma by including a `bool` with the `pexpr`.
-/
unsafe def decode_simp_arg_list_with_symm (hs : List simp_arg_type) :
    tactic <| List (pexpr × Bool) × List Name × List Name × Bool := do
  let (hs, ex, all) :=
    hs.foldl
      (fun r h =>
        match r, h with
        | (es, ex, all), simp_arg_type.all_hyps => (es, ex, true)
        | (es, ex, all), simp_arg_type.except id => (es, id :: ex, all)
        | (es, ex, all), simp_arg_type.expr e => ((e, false) :: es, ex, all)
        | (es, ex, all), simp_arg_type.symm_expr e => ((e, true) :: es, ex, all))
      ([], [], false)
  let (gex, hex) ← resolve_exception_ids all ex [] []
  return (hs, gex, hex, all)
#align tactic.decode_simp_arg_list_with_symm tactic.decode_simp_arg_list_with_symm

private unsafe def add_simps : simp_lemmas → List (Name × Bool) → tactic simp_lemmas
  | s, [] => return s
  | s, n :: ns => do
    let s' ← s.add_simp n.fst n.snd
    add_simps s' ns
#align tactic.add_simps tactic.add_simps

private unsafe def report_invalid_simp_lemma {α : Type} (n : Name) : tactic α :=
  fail
    f! "invalid simplification lemma '{n}' (use command 'set_option trace.simp_lemmas true' for more details)"
#align tactic.report_invalid_simp_lemma tactic.report_invalid_simp_lemma

private unsafe def check_no_overload (p : pexpr) : tactic Unit :=
  when p.is_choice_macro <|
    match p with
    | macro _ ps =>
      fail <|
        to_fmt "ambiguous overload, possible interpretations" ++
          format.join (ps.map fun p => (to_fmt p).indent 4)
    | _ => failed
#align tactic.check_no_overload tactic.check_no_overload

private unsafe def simp_lemmas.resolve_and_add (s : simp_lemmas) (u : List Name) (n : Name)
    (ref : pexpr) (symm : Bool) : tactic (simp_lemmas × List Name) := do
  let p ← resolve_name n
  check_no_overload p
  let-- unpack local refs
  e := p.erase_annotations.get_app_fn.erase_annotations
  match e with
    | const n _ =>
      (do
          guard ¬symm
          has_attribute `congr n
          let s ← s n
          pure (s, u)) <|>
        (do
            let b ← is_valid_simp_lemma_cnst n
            guard b
            save_const_type_info n ref
            let s ← s n symm
            return (s, u)) <|>
          (do
              let eqns ← get_eqn_lemmas_for tt n
              guard (eqns > 0)
              save_const_type_info n ref
              let s ← add_simps s (eqns fun e => (e, ff))
              return (s, u)) <|>
            (do
                let env ← get_env
                guard (env n).isSome
                return (s, n :: u)) <|>
              report_invalid_simp_lemma n
    | _ =>
      (do
          let e ← i_to_expr_no_subgoals p
          let b ← is_valid_simp_lemma e
          guard b
          try (save_type_info e ref)
          let s ← s e symm
          return (s, u)) <|>
        report_invalid_simp_lemma n
#align tactic.simp_lemmas.resolve_and_add tactic.simp_lemmas.resolve_and_add

private unsafe def simp_lemmas.add_pexpr (s : simp_lemmas) (u : List Name) (p : pexpr)
    (symm : Bool) : tactic (simp_lemmas × List Name) :=
  match p with
  | const c [] => simp_lemmas.resolve_and_add s u c p symm
  | local_const c _ _ _ => simp_lemmas.resolve_and_add s u c p symm
  | _ => do
    let new_e ← i_to_expr_no_subgoals p
    let s ← s.add new_e symm
    return (s, u)
#align tactic.simp_lemmas.add_pexpr tactic.simp_lemmas.add_pexpr

private unsafe def simp_lemmas.append_pexprs :
    simp_lemmas → List Name → List (pexpr × Bool) → tactic (simp_lemmas × List Name)
  | s, u, [] => return (s, u)
  | s, u, l :: ls => do
    let (s, u) ← simp_lemmas.add_pexpr s u l.fst l.snd
    simp_lemmas.append_pexprs s u ls
#align tactic.simp_lemmas.append_pexprs tactic.simp_lemmas.append_pexprs

unsafe def mk_simp_set_core (no_dflt : Bool) (attr_names : List Name) (hs : List simp_arg_type)
    (at_star : Bool) : tactic (Bool × simp_lemmas × List Name) := do
  let (hs, gex, hex, all_hyps) ← decode_simp_arg_list_with_symm hs
  when (all_hyps ∧ at_star ∧ Not hex) <|
      fail "A tactic of the form `simp [*, -h] at *` is currently not supported"
  let s ← join_user_simp_lemmas no_dflt attr_names
  let-- Erase `h` from the default simp set for calls of the form `simp [←h]`.
  to_erase :=
    hs.foldl
      (fun l h =>
        match h with
        | (const id _, tt) => id :: l
        | (local_const id _ _ _, tt) => id :: l
        | _ => l)
      []
  let s := s.erase to_erase
  let (s, u) ← simp_lemmas.append_pexprs s [] hs
  let s ←
    if Not at_star ∧ all_hyps then do
        let ctx ← collect_ctx_simps
        let ctx := ctx.filter fun h => h.local_uniq_name ∉ hex
        -- remove local exceptions
            s
            ctx
      else return s
  let gex
    ←-- add equational lemmas, if any
          gex.mmap
        fun n => List.cons n <$> get_eqn_lemmas_for true n
  return (all_hyps, simp_lemmas.erase s <| gex, u)
#align tactic.mk_simp_set_core tactic.mk_simp_set_core

unsafe def mk_simp_set (no_dflt : Bool) (attr_names : List Name) (hs : List simp_arg_type) :
    tactic (simp_lemmas × List Name) :=
  Prod.snd <$> mk_simp_set_core no_dflt attr_names hs false
#align tactic.mk_simp_set tactic.mk_simp_set

end MkSimpSet

namespace Interactive

open _Root_.Interactive Interactive.Types Expr

unsafe def simp_core_aux (cfg : SimpConfig) (discharger : tactic Unit) (s : simp_lemmas)
    (u : List Name) (hs : List expr) (tgt : Bool) : tactic name_set := do
  let (to_remove, lmss) ←
    @List.foldlM tactic _ (List expr × name_set) _
        (fun ⟨hs, lms⟩ h => do
          let h_type ← infer_type h
          (do
                let (new_h_type, pr, new_lms) ← simplify s u h_type cfg `eq discharger
                assert h new_h_type
                (mk_eq_mp pr h >>= tactic.exact) >> return (h :: hs, lms new_lms)) <|>
              return (hs, lms))
        ([], mk_name_set) hs
  let (lms, goal_simplified) ←
    if tgt then
        (simp_target s u cfg discharger >>= fun ns => return (ns, true)) <|>
          return (mk_name_set, false)
      else return (mk_name_set, false)
  guard (cfg = ff ∨ to_remove > 0 ∨ goal_simplified) <|> fail "simplify tactic failed to simplify"
  to_remove fun h => try (clear h)
  return (lmss lms)
#align tactic.interactive.simp_core_aux tactic.interactive.simp_core_aux

unsafe def simp_core (cfg : SimpConfig) (discharger : tactic Unit) (no_dflt : Bool)
    (hs : List simp_arg_type) (attr_names : List Name) (locat : Loc) : tactic name_set := do
  let lms ←
    match locat with
      | loc.wildcard => do
        let (all_hyps, s, u) ← mk_simp_set_core no_dflt attr_names hs true
        if all_hyps then tactic.simp_all s u cfg discharger
          else do
            let hyps ← non_dep_prop_hyps
            simp_core_aux cfg discharger s u hyps tt
      | _ => do
        let (s, u) ← mk_simp_set no_dflt attr_names hs
        let ns ← locat.get_locals
        simp_core_aux cfg discharger s u ns locat
  try tactic.triv
  try (tactic.reflexivity reducible)
  return lms
#align tactic.interactive.simp_core tactic.interactive.simp_core

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses. It has many variants.\n\n`simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.\n\n`simp [h₁ h₂ ... hₙ]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions. If `hᵢ` is preceded by left arrow (`←` or `<-`), the simplification is performed in the reverse direction. If an `hᵢ` is a defined constant `f`, then the equational lemmas associated with `f` are used. This provides a convenient way to unfold `f`.\n\n`simp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and all hypotheses.\n\n`simp *` is a shorthand for `simp [*]`.\n\n`simp only [h₁ h₂ ... hₙ]` is like `simp [h₁ h₂ ... hₙ]` but does not use `[simp]` lemmas\n\n`simp [-id_1, ... -id_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`, but removes the ones named `idᵢ`.\n\n`simp at h₁ h₂ ... hₙ` simplifies the non-dependent hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. The tactic fails if the target or another hypothesis depends on one of them. The token `⊢` or `|-` can be added to the list to include the target.\n\n`simp at *` simplifies all the hypotheses and the target.\n\n`simp * at *` simplifies target and all (non-dependent propositional) hypotheses using the other hypotheses.\n\n`simp with attr₁ ... attrₙ` simplifies the main goal target using the lemmas tagged with any of the attributes `[attr₁]`, ..., `[attrₙ]` or `[simp]`.\n-/")]
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
           (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"!\"")]) "?"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`trace_lemmas]
         [":"
          («term_<|_»
           `parse
           "<|"
           (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"?\"")]) "?"))]
         []
         ")")
        (Term.explicitBinder "(" [`no_dflt] [":" (Term.app `parse [`only_flag])] [] ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `parse [`simp_arg_list])] [] ")")
        (Term.explicitBinder "(" [`attr_names] [":" (Term.app `parse [`with_ident_list])] [] ")")
        (Term.explicitBinder "(" [`locat] [":" (Term.app `parse [`location])] [] ")")
        (Term.explicitBinder
         "("
         [`cfg]
         [":" `simp_config_ext]
         [(Term.binderDefault ":=" (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}"))]
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.let
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `cfg
          []
          []
          ":="
          (Term.match
           "match"
           []
           []
           [(Term.matchDiscr [] `use_iota_eqn) "," (Term.matchDiscr [] `trace_lemmas)]
           "with"
           (Term.matchAlts
            [(Term.matchAlt "|" [[`none "," `none]] "=>" `cfg)
             (Term.matchAlt
              "|"
              [[(Term.app `some [(Term.hole "_")]) "," `none]]
              "=>"
              (Term.structInst
               "{"
               [[`cfg] "with"]
               [(Term.structInstField (Term.structInstLVal `iotaEqn []) ":=" `true)]
               (Term.optEllipsis [])
               []
               "}"))
             (Term.matchAlt
              "|"
              [[`none "," (Term.app `some [(Term.hole "_")])]]
              "=>"
              (Term.structInst
               "{"
               [[`cfg] "with"]
               [(Term.structInstField (Term.structInstLVal `traceLemmas []) ":=" `true)]
               (Term.optEllipsis [])
               []
               "}"))
             (Term.matchAlt
              "|"
              [[(Term.app `some [(Term.hole "_")]) "," (Term.app `some [(Term.hole "_")])]]
              "=>"
              (Term.structInst
               "{"
               [[`cfg] "with"]
               [(Term.structInstField (Term.structInstLVal `iotaEqn []) ":=" `true)
                []
                (Term.structInstField (Term.structInstLVal `traceLemmas []) ":=" `true)]
               (Term.optEllipsis [])
               []
               "}"))]))))
        []
        (Term.app
         `propagate_tags
         [(Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl
                `lms
                []
                "←"
                (Term.doExpr
                 (Term.app
                  `simp_core
                  [(Term.proj `cfg "." `toSimpConfig)
                   (Term.proj `cfg "." `discharger)
                   `no_dflt
                   `hs
                   `attr_names
                   `locat]))))
              [])
             (Term.doSeqItem
              (Term.doExpr
               (termIfThenElse
                "if"
                `cfg
                "then"
                (Term.app
                 `trace
                 [(«term_++_»
                   (coeNotation "↑" (str "\"Try this: simp only \""))
                   "++"
                   (Term.app `to_fmt [`lms]))])
                "else"
                `skip))
              [])]))]))
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
         `cfg
         []
         []
         ":="
         (Term.match
          "match"
          []
          []
          [(Term.matchDiscr [] `use_iota_eqn) "," (Term.matchDiscr [] `trace_lemmas)]
          "with"
          (Term.matchAlts
           [(Term.matchAlt "|" [[`none "," `none]] "=>" `cfg)
            (Term.matchAlt
             "|"
             [[(Term.app `some [(Term.hole "_")]) "," `none]]
             "=>"
             (Term.structInst
              "{"
              [[`cfg] "with"]
              [(Term.structInstField (Term.structInstLVal `iotaEqn []) ":=" `true)]
              (Term.optEllipsis [])
              []
              "}"))
            (Term.matchAlt
             "|"
             [[`none "," (Term.app `some [(Term.hole "_")])]]
             "=>"
             (Term.structInst
              "{"
              [[`cfg] "with"]
              [(Term.structInstField (Term.structInstLVal `traceLemmas []) ":=" `true)]
              (Term.optEllipsis [])
              []
              "}"))
            (Term.matchAlt
             "|"
             [[(Term.app `some [(Term.hole "_")]) "," (Term.app `some [(Term.hole "_")])]]
             "=>"
             (Term.structInst
              "{"
              [[`cfg] "with"]
              [(Term.structInstField (Term.structInstLVal `iotaEqn []) ":=" `true)
               []
               (Term.structInstField (Term.structInstLVal `traceLemmas []) ":=" `true)]
              (Term.optEllipsis [])
              []
              "}"))]))))
       []
       (Term.app
        `propagate_tags
        [(Term.do
          "do"
          (Term.doSeqIndent
           [(Term.doSeqItem
             (Term.doLetArrow
              "let"
              []
              (Term.doIdDecl
               `lms
               []
               "←"
               (Term.doExpr
                (Term.app
                 `simp_core
                 [(Term.proj `cfg "." `toSimpConfig)
                  (Term.proj `cfg "." `discharger)
                  `no_dflt
                  `hs
                  `attr_names
                  `locat]))))
             [])
            (Term.doSeqItem
             (Term.doExpr
              (termIfThenElse
               "if"
               `cfg
               "then"
               (Term.app
                `trace
                [(«term_++_»
                  (coeNotation "↑" (str "\"Try this: simp only \""))
                  "++"
                  (Term.app `to_fmt [`lms]))])
               "else"
               `skip))
             [])]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `propagate_tags
       [(Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl
              `lms
              []
              "←"
              (Term.doExpr
               (Term.app
                `simp_core
                [(Term.proj `cfg "." `toSimpConfig)
                 (Term.proj `cfg "." `discharger)
                 `no_dflt
                 `hs
                 `attr_names
                 `locat]))))
            [])
           (Term.doSeqItem
            (Term.doExpr
             (termIfThenElse
              "if"
              `cfg
              "then"
              (Term.app
               `trace
               [(«term_++_»
                 (coeNotation "↑" (str "\"Try this: simp only \""))
                 "++"
                 (Term.app `to_fmt [`lms]))])
              "else"
              `skip))
            [])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `lms
            []
            "←"
            (Term.doExpr
             (Term.app
              `simp_core
              [(Term.proj `cfg "." `toSimpConfig)
               (Term.proj `cfg "." `discharger)
               `no_dflt
               `hs
               `attr_names
               `locat]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (termIfThenElse
            "if"
            `cfg
            "then"
            (Term.app
             `trace
             [(«term_++_»
               (coeNotation "↑" (str "\"Try this: simp only \""))
               "++"
               (Term.app `to_fmt [`lms]))])
            "else"
            `skip))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       `cfg
       "then"
       (Term.app
        `trace
        [(«term_++_»
          (coeNotation "↑" (str "\"Try this: simp only \""))
          "++"
          (Term.app `to_fmt [`lms]))])
       "else"
       `skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `trace
       [(«term_++_»
         (coeNotation "↑" (str "\"Try this: simp only \""))
         "++"
         (Term.app `to_fmt [`lms]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_» (coeNotation "↑" (str "\"Try this: simp only \"")) "++" (Term.app `to_fmt [`lms]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_fmt [`lms])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lms
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_fmt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (coeNotation "↑" (str "\"Try this: simp only \""))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"Try this: simp only \"")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (some 1024, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_++_» (coeNotation "↑" (str "\"Try this: simp only \"")) "++" (Term.app `to_fmt [`lms]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `simp_core
       [(Term.proj `cfg "." `toSimpConfig)
        (Term.proj `cfg "." `discharger)
        `no_dflt
        `hs
        `attr_names
        `locat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `locat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `cfg "." `discharger)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `cfg "." `toSimpConfig)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simp_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `propagate_tags
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `use_iota_eqn) "," (Term.matchDiscr [] `trace_lemmas)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt "|" [[`none "," `none]] "=>" `cfg)
         (Term.matchAlt
          "|"
          [[(Term.app `some [(Term.hole "_")]) "," `none]]
          "=>"
          (Term.structInst
           "{"
           [[`cfg] "with"]
           [(Term.structInstField (Term.structInstLVal `iotaEqn []) ":=" `true)]
           (Term.optEllipsis [])
           []
           "}"))
         (Term.matchAlt
          "|"
          [[`none "," (Term.app `some [(Term.hole "_")])]]
          "=>"
          (Term.structInst
           "{"
           [[`cfg] "with"]
           [(Term.structInstField (Term.structInstLVal `traceLemmas []) ":=" `true)]
           (Term.optEllipsis [])
           []
           "}"))
         (Term.matchAlt
          "|"
          [[(Term.app `some [(Term.hole "_")]) "," (Term.app `some [(Term.hole "_")])]]
          "=>"
          (Term.structInst
           "{"
           [[`cfg] "with"]
           [(Term.structInstField (Term.structInstLVal `iotaEqn []) ":=" `true)
            []
            (Term.structInstField (Term.structInstLVal `traceLemmas []) ":=" `true)]
           (Term.optEllipsis [])
           []
           "}"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`cfg] "with"]
       [(Term.structInstField (Term.structInstLVal `iotaEqn []) ":=" `true)
        []
        (Term.structInstField (Term.structInstLVal `traceLemmas []) ":=" `true)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.structInst
       "{"
       [[`cfg] "with"]
       [(Term.structInstField (Term.structInstLVal `traceLemmas []) ":=" `true)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
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
      (Term.structInst
       "{"
       [[`cfg] "with"]
       [(Term.structInstField (Term.structInstLVal `iotaEqn []) ":=" `true)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `trace_lemmas
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `use_iota_eqn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
      (Term.app `parse [`location])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `location
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
      («term_<|_» `parse "<|" (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"?\"")]) "?"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? (Term.app `tk [(str "\"?\"")]) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses. It has many variants.
      
      `simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.
      
      `simp [h₁ h₂ ... hₙ]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions. If `hᵢ` is preceded by left arrow (`←` or `<-`), the simplification is performed in the reverse direction. If an `hᵢ` is a defined constant `f`, then the equational lemmas associated with `f` are used. This provides a convenient way to unfold `f`.
      
      `simp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and all hypotheses.
      
      `simp *` is a shorthand for `simp [*]`.
      
      `simp only [h₁ h₂ ... hₙ]` is like `simp [h₁ h₂ ... hₙ]` but does not use `[simp]` lemmas
      
      `simp [-id_1, ... -id_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`, but removes the ones named `idᵢ`.
      
      `simp at h₁ h₂ ... hₙ` simplifies the non-dependent hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. The tactic fails if the target or another hypothesis depends on one of them. The token `⊢` or `|-` can be added to the list to include the target.
      
      `simp at *` simplifies all the hypotheses and the target.
      
      `simp * at *` simplifies target and all (non-dependent propositional) hypotheses using the other hypotheses.
      
      `simp with attr₁ ... attrₙ` simplifies the main goal target using the lemmas tagged with any of the attributes `[attr₁]`, ..., `[attrₙ]` or `[simp]`.
      -/
    unsafe
  def
    simp
    ( use_iota_eqn : parse <| tk "!" ? )
        ( trace_lemmas : parse <| tk "?" ? )
        ( no_dflt : parse only_flag )
        ( hs : parse simp_arg_list )
        ( attr_names : parse with_ident_list )
        ( locat : parse location )
        ( cfg : simp_config_ext := { } )
      : tactic Unit
    :=
      let
        cfg
          :=
          match
            use_iota_eqn , trace_lemmas
            with
            | none , none => cfg
              | some _ , none => { cfg with iotaEqn := true }
              | none , some _ => { cfg with traceLemmas := true }
              | some _ , some _ => { cfg with iotaEqn := true traceLemmas := true }
        propagate_tags
          do
            let lms ← simp_core cfg . toSimpConfig cfg . discharger no_dflt hs attr_names locat
              if cfg then trace ↑ "Try this: simp only " ++ to_fmt lms else skip
#align tactic.interactive.simp tactic.interactive.simp

/-- Just construct the simp set and trace it. Used for debugging.
-/
unsafe def trace_simp_set (no_dflt : parse only_flag) (hs : parse simp_arg_list)
    (attr_names : parse with_ident_list) : tactic Unit := do
  let (s, _) ← mk_simp_set no_dflt attr_names hs
  s >>= trace
#align tactic.interactive.trace_simp_set tactic.interactive.trace_simp_set

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`simp_intros h₁ h₂ ... hₙ` is similar to `intros h₁ h₂ ... hₙ` except that each hypothesis is simplified as it is introduced, and each introduced hypothesis is used to simplify later ones and the final target.\n\nAs with `simp`, a list of simplification lemmas can be provided. The modifiers `only` and `with` behave as with `simp`.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `simp_intros [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`ids]
         [":" (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident_ "*")])]
         []
         ")")
        (Term.explicitBinder "(" [`no_dflt] [":" (Term.app `parse [`only_flag])] [] ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `parse [`simp_arg_list])] [] ")")
        (Term.explicitBinder "(" [`attr_names] [":" (Term.app `parse [`with_ident_list])] [] ")")
        (Term.explicitBinder
         "("
         [`cfg]
         [":" `SimpIntrosConfig]
         [(Term.binderDefault ":=" (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}"))]
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
            (Term.doPatDecl
             (Term.tuple "(" [`s "," [`u]] ")")
             "←"
             (Term.doExpr (Term.app `mk_simp_set [`no_dflt `attr_names `hs]))
             []))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `when
             [(«term¬_» "¬" `u)
              (Term.app
               `fail
               [(termS!_
                 "s!"
                 (interpolatedStrKind
                  (interpolatedStrLitKind "\"simp_intros tactic does not support {")
                  `u
                  (interpolatedStrLitKind "}\"")))])]))
           [])
          (Term.doSeqItem (Term.doExpr (Term.app `tactic.simp_intros [`s `u `ids `cfg])) [])
          (Term.doSeqItem
           (Term.doExpr
            («term_>>_»
             (Term.app `try [`triv])
             ">>"
             (Term.app `try [(Term.app `reflexivity [`reducible])])))
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
           (Term.doPatDecl
            (Term.tuple "(" [`s "," [`u]] ")")
            "←"
            (Term.doExpr (Term.app `mk_simp_set [`no_dflt `attr_names `hs]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `when
            [(«term¬_» "¬" `u)
             (Term.app
              `fail
              [(termS!_
                "s!"
                (interpolatedStrKind
                 (interpolatedStrLitKind "\"simp_intros tactic does not support {")
                 `u
                 (interpolatedStrLitKind "}\"")))])]))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `tactic.simp_intros [`s `u `ids `cfg])) [])
         (Term.doSeqItem
          (Term.doExpr
           («term_>>_»
            (Term.app `try [`triv])
            ">>"
            (Term.app `try [(Term.app `reflexivity [`reducible])])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_»
       (Term.app `try [`triv])
       ">>"
       (Term.app `try [(Term.app `reflexivity [`reducible])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `try [(Term.app `reflexivity [`reducible])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `reflexivity [`reducible])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reducible
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `reflexivity
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `reflexivity [`reducible])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `try
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `try [`triv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `triv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `try
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `tactic.simp_intros [`s `u `ids `cfg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
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
      `u
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.simp_intros
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app
       `when
       [(«term¬_» "¬" `u)
        (Term.app
         `fail
         [(termS!_
           "s!"
           (interpolatedStrKind
            (interpolatedStrLitKind "\"simp_intros tactic does not support {")
            `u
            (interpolatedStrLitKind "}\"")))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `fail
       [(termS!_
         "s!"
         (interpolatedStrKind
          (interpolatedStrLitKind "\"simp_intros tactic does not support {")
          `u
          (interpolatedStrLitKind "}\"")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termS!_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termS!_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termS!_
       "s!"
       (interpolatedStrKind
        (interpolatedStrLitKind "\"simp_intros tactic does not support {")
        `u
        (interpolatedStrLitKind "}\"")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fail
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `fail
      [(termS!_
        "s!"
        (interpolatedStrKind
         (interpolatedStrLitKind "\"simp_intros tactic does not support {")
         `u
         (interpolatedStrLitKind "}\"")))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term¬_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term¬_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term¬_» "¬" `u)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 40 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 40, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term¬_» "¬" `u) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `when
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `mk_simp_set [`no_dflt `attr_names `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `attr_names
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `no_dflt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk_simp_set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`s "," [`u]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.binderDefault', expected 'Lean.Parser.Term.binderTactic'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `SimpIntrosConfig
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
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident_ "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident_ "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
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
      `simp_intros h₁ h₂ ... hₙ` is similar to `intros h₁ h₂ ... hₙ` except that each hypothesis is simplified as it is introduced, and each introduced hypothesis is used to simplify later ones and the final target.
      
      As with `simp`, a list of simplification lemmas can be provided. The modifiers `only` and `with` behave as with `simp`.
      -/
    unsafe
  def
    simp_intros
    ( ids : parse ident_ * )
        ( no_dflt : parse only_flag )
        ( hs : parse simp_arg_list )
        ( attr_names : parse with_ident_list )
        ( cfg : SimpIntrosConfig := { } )
      : tactic Unit
    :=
      do
        let ( s , u ) ← mk_simp_set no_dflt attr_names hs
          when ¬ u fail s! "simp_intros tactic does not support { u }"
          tactic.simp_intros s u ids cfg
          try triv >> try reflexivity reducible
#align tactic.interactive.simp_intros tactic.interactive.simp_intros

private unsafe def to_simp_arg_list (symms : List Bool) (es : List pexpr) : List simp_arg_type :=
  (symms.zip es).map fun ⟨s, e⟩ => if s then simp_arg_type.symm_expr e else simp_arg_type.expr e
#align tactic.interactive.to_simp_arg_list tactic.interactive.to_simp_arg_list

/-- `dsimp` is similar to `simp`, except that it only uses definitional equalities.
-/
unsafe def dsimp (no_dflt : parse only_flag) (es : parse simp_arg_list)
    (attr_names : parse with_ident_list) (l : parse location) (cfg : DsimpConfig := { }) :
    tactic Unit := do
  let (s, u) ← mk_simp_set no_dflt attr_names es
  match l with
    | loc.wildcard =>/- Remark: we cannot revert frozen local instances.
         We disable zeta expansion because to prevent `intron n` from failing.
         Another option is to put a "marker" at the current target, and
         implement `intro_upto_marker`. -/
    do
      let n ← revert_all
      dsimp_target s u { cfg with zeta := ff }
      intron n
    | _ => l (fun h => dsimp_hyp h s u cfg) (dsimp_target s u cfg)
#align tactic.interactive.dsimp tactic.interactive.dsimp

/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a reflexive relation, that is, a relation which has a reflexivity lemma tagged with the attribute `[refl]`. The tactic checks whether `t` and `u` are definitionally equal and then solves the goal.
-/
unsafe def reflexivity : tactic Unit :=
  tactic.reflexivity
#align tactic.interactive.reflexivity tactic.interactive.reflexivity

/-- Shorter name for the tactic `reflexivity`.
-/
unsafe def refl : tactic Unit :=
  tactic.reflexivity
#align tactic.interactive.refl tactic.interactive.refl

/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation, that is, a relation which has a symmetry lemma tagged with the attribute `[symm]`. It replaces the target with `u ~ t`.
-/
unsafe def symmetry : tactic Unit :=
  tactic.symmetry
#align tactic.interactive.symmetry tactic.interactive.symmetry

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This tactic applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation, that is, a relation which has a transitivity lemma tagged with the attribute `[trans]`.\n\n`transitivity s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`. If `s` is omitted, then a metavariable is used instead.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `transitivity [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`q]
         [":" (Term.app `parse [(Init.Meta.Interactive.term_? `texpr "?")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       («term_>>_»
        `tactic.transitivity
        ">>"
        (Term.match
         "match"
         []
         []
         [(Term.matchDiscr [] `q)]
         "with"
         (Term.matchAlts
          [(Term.matchAlt "|" [[`none]] "=>" `skip)
           (Term.matchAlt
            "|"
            [[(Term.app `some [`q])]]
            "=>"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doPatDecl
                  (Term.tuple "(" [`r "," [`lhs "," `rhs]] ")")
                  "←"
                  (Term.doExpr `target_lhs_rhs)
                  []))
                [])
               (Term.doSeqItem
                (Term.doExpr
                 («term_>>=_» (Term.app `i_to_expr [`q]) ">>=" (Term.app `unify [`rhs])))
                [])])))])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_»
       `tactic.transitivity
       ">>"
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `q)]
        "with"
        (Term.matchAlts
         [(Term.matchAlt "|" [[`none]] "=>" `skip)
          (Term.matchAlt
           "|"
           [[(Term.app `some [`q])]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`r "," [`lhs "," `rhs]] ")")
                 "←"
                 (Term.doExpr `target_lhs_rhs)
                 []))
               [])
              (Term.doSeqItem
               (Term.doExpr («term_>>=_» (Term.app `i_to_expr [`q]) ">>=" (Term.app `unify [`rhs])))
               [])])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `q)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt "|" [[`none]] "=>" `skip)
         (Term.matchAlt
          "|"
          [[(Term.app `some [`q])]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doPatDecl
                (Term.tuple "(" [`r "," [`lhs "," `rhs]] ")")
                "←"
                (Term.doExpr `target_lhs_rhs)
                []))
              [])
             (Term.doSeqItem
              (Term.doExpr («term_>>=_» (Term.app `i_to_expr [`q]) ">>=" (Term.app `unify [`rhs])))
              [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`r "," [`lhs "," `rhs]] ")")
            "←"
            (Term.doExpr `target_lhs_rhs)
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr («term_>>=_» (Term.app `i_to_expr [`q]) ">>=" (Term.app `unify [`rhs])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>=_» (Term.app `i_to_expr [`q]) ">>=" (Term.app `unify [`rhs]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unify [`rhs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rhs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unify
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 56 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 55, term))
      (Term.app `i_to_expr [`q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `i_to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 55 >? 1022, (some 1023, term) <=? (some 55, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 55, (some 56, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `target_lhs_rhs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`r "," [`lhs "," `rhs]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rhs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lhs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      `tactic.transitivity
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1024, (none, [anonymous]) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 0, term) <=? (none, [anonymous])
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
      (Term.app `parse [(Init.Meta.Interactive.term_? `texpr "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? `texpr "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      This tactic applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation, that is, a relation which has a transitivity lemma tagged with the attribute `[trans]`.
      
      `transitivity s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`. If `s` is omitted, then a metavariable is used instead.
      -/
    unsafe
  def
    transitivity
    ( q : parse texpr ? ) : tactic Unit
    :=
      tactic.transitivity
        >>
        match
          q
          with
          | none => skip
            | some q => do let ( r , lhs , rhs ) ← target_lhs_rhs i_to_expr q >>= unify rhs
#align tactic.interactive.transitivity tactic.interactive.transitivity

/--
Proves a goal with target `s = t` when `s` and `t` are equal up to the associativity and commutativity of their binary operations.
-/
unsafe def ac_reflexivity : tactic Unit :=
  tactic.ac_refl
#align tactic.interactive.ac_reflexivity tactic.interactive.ac_reflexivity

/-- An abbreviation for `ac_reflexivity`.
-/
unsafe def ac_refl : tactic Unit :=
  tactic.ac_refl
#align tactic.interactive.ac_refl tactic.interactive.ac_refl

/-- Tries to prove the main goal using congruence closure.
-/
unsafe def cc : tactic Unit :=
  tactic.cc
#align tactic.interactive.cc tactic.interactive.cc

/--
Given hypothesis `h : x = t` or `h : t = x`, where `x` is a local constant, `subst h` substitutes `x` by `t` everywhere in the main goal and then clears `h`.
-/
unsafe def subst (q : parse texpr) : tactic Unit :=
  (i_to_expr q >>= tactic.subst) >> try (tactic.reflexivity reducible)
#align tactic.interactive.subst tactic.interactive.subst

/-- Apply `subst` to all hypotheses of the form `h : x = t` or `h : t = x`.
-/
unsafe def subst_vars : tactic Unit :=
  tactic.subst_vars
#align tactic.interactive.subst_vars tactic.interactive.subst_vars

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`clear h₁ ... hₙ` tries to clear each hypothesis `hᵢ` from the local context.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `clear [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
          "→"
          (Term.app `tactic [`Unit])))])
      (Command.declValSimple ":=" `tactic.clear_lst [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.clear_lst
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
       "→"
       (Term.app `tactic [`Unit]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `clear h₁ ... hₙ` tries to clear each hypothesis `hᵢ` from the local context.
      -/
    unsafe
  def clear : parse ident * → tactic Unit := tactic.clear_lst
#align tactic.interactive.clear tactic.interactive.clear

private unsafe def to_qualified_name_core : Name → List Name → tactic Name
  | n, [] => fail <| "unknown declaration '" ++ toString n ++ "'"
  | n, ns :: nss => do
    let curr ← return <| ns ++ n
    let env ← get_env
    if env curr then return curr else to_qualified_name_core n nss
#align tactic.interactive.to_qualified_name_core tactic.interactive.to_qualified_name_core

private unsafe def to_qualified_name (n : Name) : tactic Name := do
  let env ← get_env
  if env n then return n
    else do
      let ns ← open_namespaces
      to_qualified_name_core n ns
#align tactic.interactive.to_qualified_name tactic.interactive.to_qualified_name

private unsafe def to_qualified_names : List Name → tactic (List Name)
  | [] => return []
  | c :: cs => do
    let new_c ← to_qualified_name c
    let new_cs ← to_qualified_names cs
    return (new_c :: new_cs)
#align tactic.interactive.to_qualified_names tactic.interactive.to_qualified_names

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Similar to `unfold`, but only uses definitional equalities.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `dunfold [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`cs]
         [":" (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])]
         []
         ")")
        (Term.explicitBinder "(" [`l] [":" (Term.app `parse [`location])] [] ")")
        (Term.explicitBinder
         "("
         [`cfg]
         [":" `DunfoldConfig]
         [(Term.binderDefault ":=" (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}"))]
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.match
        "match"
        []
        []
        [(Term.matchDiscr [] `l)]
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`loc.wildcard]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `ls [] "←" (Term.doExpr `tactic.local_context)))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert_lst [`ls]))))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `new_cs [] "←" (Term.doExpr (Term.app `to_qualified_names [`cs]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `dunfold_target [`new_cs `cfg])) [])
              (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])])))
          (Term.matchAlt
           "|"
           [[(Term.hole "_")]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `new_cs [] "←" (Term.doExpr (Term.app `to_qualified_names [`cs]))))
               [])
              (Term.doSeqItem
               (Term.doExpr
                (Term.app
                 `l
                 [(Term.fun
                   "fun"
                   (Term.basicFun [`h] [] "=>" (Term.app `dunfold_hyp [`cs `h `cfg])))
                  (Term.app `dunfold_target [`new_cs `cfg])]))
               [])])))]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `l)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[`loc.wildcard]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `ls [] "←" (Term.doExpr `tactic.local_context)))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert_lst [`ls]))))
              [])
             (Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `new_cs [] "←" (Term.doExpr (Term.app `to_qualified_names [`cs]))))
              [])
             (Term.doSeqItem (Term.doExpr (Term.app `dunfold_target [`new_cs `cfg])) [])
             (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])])))
         (Term.matchAlt
          "|"
          [[(Term.hole "_")]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doIdDecl `new_cs [] "←" (Term.doExpr (Term.app `to_qualified_names [`cs]))))
              [])
             (Term.doSeqItem
              (Term.doExpr
               (Term.app
                `l
                [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.app `dunfold_hyp [`cs `h `cfg])))
                 (Term.app `dunfold_target [`new_cs `cfg])]))
              [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `new_cs [] "←" (Term.doExpr (Term.app `to_qualified_names [`cs]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `l
            [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.app `dunfold_hyp [`cs `h `cfg])))
             (Term.app `dunfold_target [`new_cs `cfg])]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `l
       [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.app `dunfold_hyp [`cs `h `cfg])))
        (Term.app `dunfold_target [`new_cs `cfg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dunfold_target [`new_cs `cfg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `new_cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dunfold_target
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `dunfold_target [`new_cs `cfg])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.app `dunfold_hyp [`cs `h `cfg])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dunfold_hyp [`cs `h `cfg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
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
      `cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dunfold_hyp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.app `dunfold_hyp [`cs `h `cfg])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `to_qualified_names [`cs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_qualified_names
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `ls [] "←" (Term.doExpr `tactic.local_context)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert_lst [`ls]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `new_cs [] "←" (Term.doExpr (Term.app `to_qualified_names [`cs]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `dunfold_target [`new_cs `cfg])) [])
         (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `intron [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intron
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `dunfold_target [`new_cs `cfg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `new_cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dunfold_target
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `to_qualified_names [`cs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_qualified_names
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `revert_lst [`ls])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ls
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `revert_lst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `tactic.local_context
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `loc.wildcard
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.binderDefault', expected 'Lean.Parser.Term.binderTactic'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `DunfoldConfig
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [`location])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `location
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
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
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
      Similar to `unfold`, but only uses definitional equalities.
      -/
    unsafe
  def
    dunfold
    ( cs : parse ident * ) ( l : parse location ) ( cfg : DunfoldConfig := { } ) : tactic Unit
    :=
      match
        l
        with
        |
            loc.wildcard
            =>
            do
              let ls ← tactic.local_context
                let n ← revert_lst ls
                let new_cs ← to_qualified_names cs
                dunfold_target new_cs cfg
                intron n
          |
            _
            =>
            do
              let new_cs ← to_qualified_names cs
                l fun h => dunfold_hyp cs h cfg dunfold_target new_cs cfg
#align tactic.interactive.dunfold tactic.interactive.dunfold

private unsafe def delta_hyps : List Name → List Name → tactic Unit
  | cs, [] => skip
  | cs, h :: hs => (get_local h >>= delta_hyp cs) >> delta_hyps cs hs
#align tactic.interactive.delta_hyps tactic.interactive.delta_hyps

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Similar to `dunfold`, but performs a raw delta reduction, rather than using an equation associated with the defined constants.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `delta [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
          "→"
          (Term.arrow (Term.app `parse [`location]) "→" (Term.app `tactic [`Unit]))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`cs "," `loc.wildcard]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `ls [] "←" (Term.doExpr `tactic.local_context)))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert_lst [`ls]))))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `new_cs [] "←" (Term.doExpr (Term.app `to_qualified_names [`cs]))))
               [])
              (Term.doSeqItem (Term.doExpr (Term.app `delta_target [`new_cs])) [])
              (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])])))
          (Term.matchAlt
           "|"
           [[`cs "," `l]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doIdDecl `new_cs [] "←" (Term.doExpr (Term.app `to_qualified_names [`cs]))))
               [])
              (Term.doSeqItem
               (Term.doExpr
                (Term.app `l [(Term.app `delta_hyp [`new_cs]) (Term.app `delta_target [`new_cs])]))
               [])])))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `new_cs [] "←" (Term.doExpr (Term.app `to_qualified_names [`cs]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app `l [(Term.app `delta_hyp [`new_cs]) (Term.app `delta_target [`new_cs])]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `l [(Term.app `delta_hyp [`new_cs]) (Term.app `delta_target [`new_cs])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `delta_target [`new_cs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `new_cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `delta_target
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `delta_target [`new_cs]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `delta_hyp [`new_cs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `new_cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `delta_hyp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `delta_hyp [`new_cs]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `to_qualified_names [`cs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_qualified_names
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow "let" [] (Term.doIdDecl `ls [] "←" (Term.doExpr `tactic.local_context)))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `n [] "←" (Term.doExpr (Term.app `revert_lst [`ls]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `new_cs [] "←" (Term.doExpr (Term.app `to_qualified_names [`cs]))))
          [])
         (Term.doSeqItem (Term.doExpr (Term.app `delta_target [`new_cs])) [])
         (Term.doSeqItem (Term.doExpr (Term.app `intron [`n])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `intron [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intron
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `delta_target [`new_cs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `new_cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `delta_target
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `to_qualified_names [`cs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_qualified_names
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `revert_lst [`ls])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ls
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `revert_lst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `tactic.local_context
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `loc.wildcard
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
       "→"
       (Term.arrow (Term.app `parse [`location]) "→" (Term.app `tactic [`Unit])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `parse [`location]) "→" (Term.app `tactic [`Unit]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `parse [`location])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `location
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `parse
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Similar to `dunfold`, but performs a raw delta reduction, rather than using an equation associated with the defined constants.
      -/
    unsafe
  def
    delta
    : parse ident * → parse location → tactic Unit
    |
        cs , loc.wildcard
        =>
        do
          let ls ← tactic.local_context
            let n ← revert_lst ls
            let new_cs ← to_qualified_names cs
            delta_target new_cs
            intron n
      | cs , l => do let new_cs ← to_qualified_names cs l delta_hyp new_cs delta_target new_cs
#align tactic.interactive.delta tactic.interactive.delta

private unsafe def unfold_projs_hyps (cfg : UnfoldProjConfig := { }) (hs : List Name) :
    tactic Bool :=
  hs.mfoldl
    (fun r h => do
      let h ← get_local h
      unfold_projs_hyp h cfg >> return tt <|> return r)
    false
#align tactic.interactive.unfold_projs_hyps tactic.interactive.unfold_projs_hyps

/-- This tactic unfolds all structure projections.
-/
unsafe def unfold_projs (l : parse location) (cfg : UnfoldProjConfig := { }) : tactic Unit :=
  match l with
  | loc.wildcard => do
    let ls ← local_context
    let b₁ ← unfold_projs_hyps cfg (ls.map expr.local_pp_name)
    let b₂ ← tactic.unfold_projs_target cfg >> return true <|> return false
    when (Not b₁ ∧ Not b₂) (fail "unfold_projs failed to simplify")
  | _ =>
    l.try_apply (fun h => unfold_projs_hyp h cfg) (tactic.unfold_projs_target cfg) <|>
      fail "unfold_projs failed to simplify"
#align tactic.interactive.unfold_projs tactic.interactive.unfold_projs

end Interactive

unsafe def ids_to_simp_arg_list (tac_name : Name) (cs : List Name) : tactic (List simp_arg_type) :=
  cs.mmap fun c => do
    let n ← resolve_name c
    let hs ← get_eqn_lemmas_for false n.const_name
    let env ← get_env
    let p := env.is_projection n.const_name
    when (hs ∧ p)
        (fail
          s! "{tac_name } tactic failed, {c} does not have equational lemmas nor is a projection")
    return <| simp_arg_type.expr (expr.const c [])
#align tactic.ids_to_simp_arg_list tactic.ids_to_simp_arg_list

structure UnfoldConfig extends SimpConfig where
  zeta := false
  proj := false
  eta := false
  canonizeInstances := false
  constructorEq := false
#align tactic.unfold_config Tactic.UnfoldConfig

namespace Interactive

open _Root_.Interactive Interactive.Types Expr

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given defined constants `e₁ ... eₙ`, `unfold e₁ ... eₙ` iteratively unfolds all occurrences in the target of the main goal, using equational lemmas associated with the definitions.\n\nAs with `simp`, the `at` modifier can be used to specify locations for the unfolding.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `unfold [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`cs]
         [":" (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])]
         []
         ")")
        (Term.explicitBinder "(" [`locat] [":" (Term.app `parse [`location])] [] ")")
        (Term.explicitBinder
         "("
         [`cfg]
         [":" `UnfoldConfig]
         [(Term.binderDefault ":=" (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}"))]
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
             `es
             []
             "←"
             (Term.doExpr (Term.app `ids_to_simp_arg_list [(str "\"unfold\"") `cs]))))
           [])
          (Term.doSeqItem
           (Term.doLet "let" [] (Term.letDecl (Term.letIdDecl `no_dflt [] [] ":=" `true)))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app `simp_core [`cfg `failed `no_dflt `es («term[_]» "[" [] "]") `locat]))
           [])
          (Term.doSeqItem (Term.doExpr `skip) [])]))
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
            `es
            []
            "←"
            (Term.doExpr (Term.app `ids_to_simp_arg_list [(str "\"unfold\"") `cs]))))
          [])
         (Term.doSeqItem
          (Term.doLet "let" [] (Term.letDecl (Term.letIdDecl `no_dflt [] [] ":=" `true)))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app `simp_core [`cfg `failed `no_dflt `es («term[_]» "[" [] "]") `locat]))
          [])
         (Term.doSeqItem (Term.doExpr `skip) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `simp_core [`cfg `failed `no_dflt `es («term[_]» "[" [] "]") `locat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `locat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `es
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `no_dflt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `failed
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `simp_core
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      `true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `ids_to_simp_arg_list [(str "\"unfold\"") `cs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (str "\"unfold\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ids_to_simp_arg_list
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.binderDefault', expected 'Lean.Parser.Term.binderTactic'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UnfoldConfig
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [`location])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `location
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
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
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
      Given defined constants `e₁ ... eₙ`, `unfold e₁ ... eₙ` iteratively unfolds all occurrences in the target of the main goal, using equational lemmas associated with the definitions.
      
      As with `simp`, the `at` modifier can be used to specify locations for the unfolding.
      -/
    unsafe
  def
    unfold
    ( cs : parse ident * ) ( locat : parse location ) ( cfg : UnfoldConfig := { } ) : tactic Unit
    :=
      do
        let es ← ids_to_simp_arg_list "unfold" cs
          let no_dflt := true
          simp_core cfg failed no_dflt es [ ] locat
          skip
#align tactic.interactive.unfold tactic.interactive.unfold

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Similar to `unfold`, but does not iterate the unfolding.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `unfold1 [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`cs]
         [":" (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])]
         []
         ")")
        (Term.explicitBinder "(" [`locat] [":" (Term.app `parse [`location])] [] ")")
        (Term.explicitBinder
         "("
         [`cfg]
         [":" `UnfoldConfig]
         [(Term.binderDefault
           ":="
           (Term.structInst
            "{"
            []
            [(Term.structInstField (Term.structInstLVal `singlePass []) ":=" `true)]
            (Term.optEllipsis [])
            []
            "}"))]
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple ":=" (Term.app `unfold [`cs `locat `cfg]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unfold [`cs `locat `cfg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cfg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `locat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unfold
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.binderDefault', expected 'Lean.Parser.Term.binderTactic'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `singlePass []) ":=" `true)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UnfoldConfig
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [`location])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `location
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
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
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
      Similar to `unfold`, but does not iterate the unfolding.
      -/
    unsafe
  def
    unfold1
    ( cs : parse ident * )
        ( locat : parse location )
        ( cfg : UnfoldConfig := { singlePass := true } )
      : tactic Unit
    := unfold cs locat cfg
#align tactic.interactive.unfold1 tactic.interactive.unfold1

/-- If the target of the main goal is an `opt_param`, assigns the default value.
-/
unsafe def apply_opt_param : tactic Unit :=
  tactic.apply_opt_param
#align tactic.interactive.apply_opt_param tactic.interactive.apply_opt_param

/-- If the target of the main goal is an `auto_param`, executes the associated tactic.
-/
unsafe def apply_auto_param : tactic Unit :=
  tactic.apply_auto_param
#align tactic.interactive.apply_auto_param tactic.interactive.apply_auto_param

/-- Fails if the given tactic succeeds.
-/
unsafe def fail_if_success (tac : itactic) : tactic Unit :=
  tactic.fail_if_success tac
#align tactic.interactive.fail_if_success tactic.interactive.fail_if_success

/-- Succeeds if the given tactic fails.
-/
unsafe def success_if_fail (tac : itactic) : tactic Unit :=
  tactic.success_if_fail tac
#align tactic.interactive.success_if_fail tactic.interactive.success_if_fail

unsafe def guard_expr_eq (t : expr) (p : parse <| tk ":=" *> texpr) : tactic Unit := do
  let e ← to_expr p
  guard (alpha_eqv t e)
#align tactic.interactive.guard_expr_eq tactic.interactive.guard_expr_eq

/-- `guard_target t` fails if the target of the main goal is not `t`.
We use this tactic for writing tests.
-/
unsafe def guard_target (p : parse texpr) : tactic Unit := do
  let t ← target
  guard_expr_eq t p
#align tactic.interactive.guard_target tactic.interactive.guard_target

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`guard_hyp h : t` fails if the hypothesis `h` does not have type `t`.\nWe use this tactic for writing tests.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `guard_hyp [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`n] [":" (Term.app `parse [`ident])] [] ")")
        (Term.explicitBinder
         "("
         [`ty]
         [":"
          (Term.app
           `parse
           [(Init.Meta.Interactive.term_?
             («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `texpr)
             "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`val]
         [":"
          (Term.app
           `parse
           [(Init.Meta.Interactive.term_?
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
            (Term.doIdDecl `h [] "←" (Term.doExpr (Term.app `get_local [`n]))))
           [])
          (Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl
             `ldecl
             []
             "←"
             (Term.doExpr
              (Term.app
               `tactic.unsafe.type_context.run
               [(Term.do
                 "do"
                 (Term.doSeqIndent
                  [(Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doIdDecl
                      `lctx
                      []
                      "←"
                      (Term.doExpr `unsafe.type_context.get_local_context)))
                    [])
                   (Term.doSeqItem
                    (Term.doExpr («term_<|_» `pure "<|" (Term.app `lctx [`h])))
                    [])]))]))))
           [])
          (Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doPatDecl
             `ldecl
             "←"
             (Term.doExpr `ldecl)
             ["|"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doExpr
                  (Term.app
                   `fail
                   [(Std.termF!_
                     "f!"
                     (interpolatedStrKind
                      (interpolatedStrLitKind "\"hypothesis {")
                      `h
                      (interpolatedStrLitKind "} not found\"")))]))
                 [])])]))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.match
             "match"
             []
             []
             [(Term.matchDiscr [] `ty)]
             "with"
             (Term.matchAlts
              [(Term.matchAlt
                "|"
                [[(Term.app `some [`p])]]
                "=>"
                (Term.app `guard_expr_eq [`ldecl `p]))
               (Term.matchAlt "|" [[`none]] "=>" `skip)])))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.match
             "match"
             []
             []
             [(Term.matchDiscr [] `ldecl) "," (Term.matchDiscr [] `val)]
             "with"
             (Term.matchAlts
              [(Term.matchAlt
                "|"
                [[`none "," (Term.app `some [(Term.hole "_")])]]
                "=>"
                (Term.app
                 `fail
                 [(Std.termF!_
                   "f!"
                   (interpolatedStrKind
                    (interpolatedStrLitKind "\"{")
                    `h
                    (interpolatedStrLitKind "} is not a let binding\"")))]))
               (Term.matchAlt
                "|"
                [[(Term.app `some [(Term.hole "_")]) "," `none]]
                "=>"
                (Term.app
                 `fail
                 [(Std.termF!_
                   "f!"
                   (interpolatedStrKind
                    (interpolatedStrLitKind "\"{")
                    `h
                    (interpolatedStrLitKind "} is a let binding\"")))]))
               (Term.matchAlt
                "|"
                [[(Term.app `some [`hval]) "," (Term.app `some [`val])]]
                "=>"
                (Term.app `guard_expr_eq [`hval `val]))
               (Term.matchAlt "|" [[`none "," `none]] "=>" `skip)])))
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
           (Term.doIdDecl `h [] "←" (Term.doExpr (Term.app `get_local [`n]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `ldecl
            []
            "←"
            (Term.doExpr
             (Term.app
              `tactic.unsafe.type_context.run
              [(Term.do
                "do"
                (Term.doSeqIndent
                 [(Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doIdDecl
                     `lctx
                     []
                     "←"
                     (Term.doExpr `unsafe.type_context.get_local_context)))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr («term_<|_» `pure "<|" (Term.app `lctx [`h])))
                   [])]))]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            `ldecl
            "←"
            (Term.doExpr `ldecl)
            ["|"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doExpr
                 (Term.app
                  `fail
                  [(Std.termF!_
                    "f!"
                    (interpolatedStrKind
                     (interpolatedStrLitKind "\"hypothesis {")
                     `h
                     (interpolatedStrLitKind "} not found\"")))]))
                [])])]))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.match
            "match"
            []
            []
            [(Term.matchDiscr [] `ty)]
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [[(Term.app `some [`p])]]
               "=>"
               (Term.app `guard_expr_eq [`ldecl `p]))
              (Term.matchAlt "|" [[`none]] "=>" `skip)])))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.match
            "match"
            []
            []
            [(Term.matchDiscr [] `ldecl) "," (Term.matchDiscr [] `val)]
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [[`none "," (Term.app `some [(Term.hole "_")])]]
               "=>"
               (Term.app
                `fail
                [(Std.termF!_
                  "f!"
                  (interpolatedStrKind
                   (interpolatedStrLitKind "\"{")
                   `h
                   (interpolatedStrLitKind "} is not a let binding\"")))]))
              (Term.matchAlt
               "|"
               [[(Term.app `some [(Term.hole "_")]) "," `none]]
               "=>"
               (Term.app
                `fail
                [(Std.termF!_
                  "f!"
                  (interpolatedStrKind
                   (interpolatedStrLitKind "\"{")
                   `h
                   (interpolatedStrLitKind "} is a let binding\"")))]))
              (Term.matchAlt
               "|"
               [[(Term.app `some [`hval]) "," (Term.app `some [`val])]]
               "=>"
               (Term.app `guard_expr_eq [`hval `val]))
              (Term.matchAlt "|" [[`none "," `none]] "=>" `skip)])))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `ldecl) "," (Term.matchDiscr [] `val)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[`none "," (Term.app `some [(Term.hole "_")])]]
          "=>"
          (Term.app
           `fail
           [(Std.termF!_
             "f!"
             (interpolatedStrKind
              (interpolatedStrLitKind "\"{")
              `h
              (interpolatedStrLitKind "} is not a let binding\"")))]))
         (Term.matchAlt
          "|"
          [[(Term.app `some [(Term.hole "_")]) "," `none]]
          "=>"
          (Term.app
           `fail
           [(Std.termF!_
             "f!"
             (interpolatedStrKind
              (interpolatedStrLitKind "\"{")
              `h
              (interpolatedStrLitKind "} is a let binding\"")))]))
         (Term.matchAlt
          "|"
          [[(Term.app `some [`hval]) "," (Term.app `some [`val])]]
          "=>"
          (Term.app `guard_expr_eq [`hval `val]))
         (Term.matchAlt "|" [[`none "," `none]] "=>" `skip)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `guard_expr_eq [`hval `val])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `val
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hval
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `guard_expr_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`val])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `val
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`hval])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hval
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `fail
       [(Std.termF!_
         "f!"
         (interpolatedStrKind
          (interpolatedStrLitKind "\"{")
          `h
          (interpolatedStrLitKind "} is a let binding\"")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.termF!_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.termF!_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.termF!_
       "f!"
       (interpolatedStrKind
        (interpolatedStrLitKind "\"{")
        `h
        (interpolatedStrLitKind "} is a let binding\"")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fail
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `fail
       [(Std.termF!_
         "f!"
         (interpolatedStrKind
          (interpolatedStrLitKind "\"{")
          `h
          (interpolatedStrLitKind "} is not a let binding\"")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.termF!_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.termF!_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.termF!_
       "f!"
       (interpolatedStrKind
        (interpolatedStrLitKind "\"{")
        `h
        (interpolatedStrLitKind "} is not a let binding\"")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fail
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ldecl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] `ty)]
       "with"
       (Term.matchAlts
        [(Term.matchAlt "|" [[(Term.app `some [`p])]] "=>" (Term.app `guard_expr_eq [`ldecl `p]))
         (Term.matchAlt "|" [[`none]] "=>" `skip)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `guard_expr_eq [`ldecl `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ldecl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `guard_expr_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
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
      `ty
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `fail
       [(Std.termF!_
         "f!"
         (interpolatedStrKind
          (interpolatedStrLitKind "\"hypothesis {")
          `h
          (interpolatedStrLitKind "} not found\"")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.termF!_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Std.termF!_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.termF!_
       "f!"
       (interpolatedStrKind
        (interpolatedStrLitKind "\"hypothesis {")
        `h
        (interpolatedStrLitKind "} not found\"")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fail
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ldecl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ldecl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       `tactic.unsafe.type_context.run
       [(Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doIdDecl `lctx [] "←" (Term.doExpr `unsafe.type_context.get_local_context)))
            [])
           (Term.doSeqItem (Term.doExpr («term_<|_» `pure "<|" (Term.app `lctx [`h]))) [])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl `lctx [] "←" (Term.doExpr `unsafe.type_context.get_local_context)))
          [])
         (Term.doSeqItem (Term.doExpr («term_<|_» `pure "<|" (Term.app `lctx [`h]))) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `pure "<|" (Term.app `lctx [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lctx [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lctx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `pure
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      `unsafe.type_context.get_local_context
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, doElem)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.unsafe.type_context.run
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `get_local [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_local
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
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
       [(Init.Meta.Interactive.term_?
         («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr)
         "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? («term_*>_» (Term.app `tk [(str "\":=\"")]) "*>" `texpr) "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      `guard_hyp h : t` fails if the hypothesis `h` does not have type `t`.
      We use this tactic for writing tests.
      -/
    unsafe
  def
    guard_hyp
    ( n : parse ident ) ( ty : parse tk ":" *> texpr ? ) ( val : parse tk ":=" *> texpr ? )
      : tactic Unit
    :=
      do
        let h ← get_local n
          let
            ldecl
              ←
              tactic.unsafe.type_context.run
                do let lctx ← unsafe.type_context.get_local_context pure <| lctx h
          let ldecl ← ldecl | fail f! "hypothesis { h } not found"
          match ty with | some p => guard_expr_eq ldecl p | none => skip
          match
            ldecl , val
            with
            | none , some _ => fail f! "{ h } is not a let binding"
              | some _ , none => fail f! "{ h } is a let binding"
              | some hval , some val => guard_expr_eq hval val
              | none , none => skip
#align tactic.interactive.guard_hyp tactic.interactive.guard_hyp

/-- `match_target t` fails if target does not match pattern `t`.
-/
unsafe def match_target (t : parse texpr) (m := reducible) : tactic Unit :=
  tactic.match_target t m >> skip
#align tactic.interactive.match_target tactic.interactive.match_target

/-- `by_cases p` splits the main goal into two cases, assuming `h : p` in the first branch, and
`h : ¬ p` in the second branch. You can specify the name of the new hypothesis using the syntax
`by_cases h : p`.
-/
unsafe def by_cases : parse cases_arg_p → tactic Unit
  | (n, q) =>
    concat_tags do
      let p ← tactic.to_expr_strict q
      tactic.by_cases p (n `h)
      let pos_g :: neg_g :: rest ← get_goals
      return [(`pos, pos_g), (`neg, neg_g)]
#align tactic.interactive.by_cases tactic.interactive.by_cases

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Apply function extensionality and introduce new hypotheses.\nThe tactic `funext` will keep applying new the `funext` lemma until the goal target is not reducible to\n```\n  |-  ((fun x, ...) = (fun x, ...))\n```\nThe variant `funext h₁ ... hₙ` applies `funext` `n` times, and uses the given identifiers to name the new hypotheses.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `funext [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident_ "*")])
          "→"
          (Term.app `tactic [`Unit])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" («term_>>_» `tactic.funext ">>" `skip))
          (Term.matchAlt "|" [[`hs]] "=>" («term_>>_» (Term.app `funext_lst [`hs]) ">>" `skip))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>>_» (Term.app `funext_lst [`hs]) ">>" `skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app `funext_lst [`hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext_lst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_>>_» `tactic.funext ">>" `skip)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `skip
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      `tactic.funext
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1024, (none, [anonymous]) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 60, (some 60,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident_ "*")])
       "→"
       (Term.app `tactic [`Unit]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `parse [(Init.Meta.Interactive.«term_*» `ident_ "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.«term_*» `ident_ "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.«term_*»', expected 'Init.Meta.Interactive.term_*._@.Init.Meta.Interactive._hyg.55'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Apply function extensionality and introduce new hypotheses.
      The tactic `funext` will keep applying new the `funext` lemma until the goal target is not reducible to
      ```
        |-  ((fun x, ...) = (fun x, ...))
      ```
      The variant `funext h₁ ... hₙ` applies `funext` `n` times, and uses the given identifiers to name the new hypotheses.
      -/
    unsafe
  def
    funext
    : parse ident_ * → tactic Unit
    | [ ] => tactic.funext >> skip | hs => funext_lst hs >> skip
#align tactic.interactive.funext tactic.interactive.funext

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If the target of the main goal is a proposition `p`, `by_contradiction` reduces the goal to proving `false` using the additional hypothesis `h : ¬ p`. `by_contradiction h` can be used to name the hypothesis `h : ¬ p`.\n\nThis tactic will attempt to use decidability of `p` if available, and will otherwise fall back on classical reasoning.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `by_contradiction [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`n]
         [":" (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Init.Control.Functor.«term_$>_»
        (Term.app
         `tactic.by_contradiction
         [(Term.app (Term.proj `n "." `getOrElse) [(Term.quotedName (name "`h"))])])
        " $> "
        (Term.tuple "(" [] ")"))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Control.Functor.«term_$>_»
       (Term.app
        `tactic.by_contradiction
        [(Term.app (Term.proj `n "." `getOrElse) [(Term.quotedName (name "`h"))])])
       " $> "
       (Term.tuple "(" [] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [] ")")
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app
       `tactic.by_contradiction
       [(Term.app (Term.proj `n "." `getOrElse) [(Term.quotedName (name "`h"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `n "." `getOrElse) [(Term.quotedName (name "`h"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.quotedName', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.quotedName (name "`h"))
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `n "." `getOrElse)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `n "." `getOrElse) [(Term.quotedName (name "`h"))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.by_contradiction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (none, [anonymous])
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
      (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? `ident "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      If the target of the main goal is a proposition `p`, `by_contradiction` reduces the goal to proving `false` using the additional hypothesis `h : ¬ p`. `by_contradiction h` can be used to name the hypothesis `h : ¬ p`.
      
      This tactic will attempt to use decidability of `p` if available, and will otherwise fall back on classical reasoning.
      -/
    unsafe
  def
    by_contradiction
    ( n : parse ident ? ) : tactic Unit
    := tactic.by_contradiction n . getOrElse `h $> ( )
#align tactic.interactive.by_contradiction tactic.interactive.by_contradiction

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If the target of the main goal is a proposition `p`, `by_contra` reduces the goal to proving `false` using the additional hypothesis `h : ¬ p`. `by_contra h` can be used to name the hypothesis `h : ¬ p`.\n\nThis tactic will attempt to use decidability of `p` if available, and will otherwise fall back on classical reasoning.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `by_contra [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`n]
         [":" (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple ":=" (Term.app `by_contradiction [`n]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `by_contradiction [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `by_contradiction
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
      (Term.app `parse [(Init.Meta.Interactive.term_? `ident "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Meta.Interactive.term_? `ident "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Meta.Interactive.term_?', expected 'Init.Meta.Interactive.term_?._@.Init.Meta.Interactive._hyg.10'
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
      If the target of the main goal is a proposition `p`, `by_contra` reduces the goal to proving `false` using the additional hypothesis `h : ¬ p`. `by_contra h` can be used to name the hypothesis `h : ¬ p`.
      
      This tactic will attempt to use decidability of `p` if available, and will otherwise fall back on classical reasoning.
      -/
    unsafe
  def by_contra ( n : parse ident ? ) : tactic Unit := by_contradiction n
#align tactic.interactive.by_contra tactic.interactive.by_contra

/-- Type check the given expression, and trace its type.
-/
unsafe def type_check (p : parse texpr) : tactic Unit := do
  let e ← to_expr p
  tactic.type_check e
  infer_type e >>= trace
#align tactic.interactive.type_check tactic.interactive.type_check

/-- Fail if there are unsolved goals.
-/
unsafe def done : tactic Unit :=
  tactic.done
#align tactic.interactive.done tactic.interactive.done

private unsafe def show_aux (p : pexpr) : List expr → List expr → tactic Unit
  | [], r => fail "show tactic failed"
  | g :: gs, r => do
    (do
          set_goals [g]
          let g_ty ← target
          let ty ← i_to_expr p
          unify g_ty ty
          set_goals (g :: r ++ gs)
          tactic.change ty) <|>
        show_aux gs (g :: r)
#align tactic.interactive.show_aux tactic.interactive.show_aux

/--
`show t` finds the first goal whose target unifies with `t`. It makes that the main goal, performs the unification, and replaces the target with the unified version of `t`.
-/
unsafe def show (q : parse texpr) : tactic Unit := do
  let gs ← get_goals
  show_aux q gs []
#align tactic.interactive.show tactic.interactive.show

/--
The tactic `specialize h a₁ ... aₙ` works on local hypothesis `h`. The premises of this hypothesis, either universal quantifications or non-dependent implications, are instantiated by concrete terms coming either from arguments `a₁` ... `aₙ`. The tactic adds a new hypothesis with the same name `h := h a₁ ... aₙ` and tries to clear the previous one.
-/
unsafe def specialize (p : parse texpr) : tactic Unit :=
  focus1 do
    let e ← i_to_expr p
    let h := expr.get_app_fn e
    if h then (tactic.note h none e >> try (tactic.clear h)) >> rotate 1
      else
        tactic.fail
          "specialize requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"
#align tactic.interactive.specialize tactic.interactive.specialize

unsafe def congr :=
  tactic.congr
#align tactic.interactive.congr tactic.interactive.congr

end Interactive

end Tactic

section AddInteractive

open Tactic

-- See add_interactive
private unsafe def add_interactive_aux (new_namespace : Name) : List Name → Tactic
  | [] => return ()
  | n :: ns => do
    let env ← get_env
    let d_name ← resolve_constant n
    let declaration.defn _ ls ty val hints trusted ← env.get d_name
    let Name.mk_string h _ ← return d_name
    let new_name := .str new_namespace h
    add_decl (declaration.defn new_name ls ty (expr.const d_name (ls level.param)) hints trusted)
    (do
          let doc ← doc_string d_name
          add_doc_string new_name doc) <|>
        skip
    add_interactive_aux ns
#align add_interactive_aux add_interactive_aux

/-- Copy a list of meta definitions in the current namespace to tactic.interactive.

This command is useful when we want to update tactic.interactive without closing the current namespace.
-/
unsafe def add_interactive (ns : List Name) (p : Name := `tactic.interactive) : Tactic :=
  add_interactive_aux p ns
#align add_interactive add_interactive

unsafe def has_dup : tactic Bool := do
  let ctx ← local_context
  let p : name_set × Bool :=
    ctx.foldl
      (fun ⟨s, r⟩ h =>
        if r then (s, r)
        else if s.contains h.local_pp_name then (s, true) else (s.insert h.local_pp_name, false))
      (mk_name_set, false)
  return p.2
#align has_dup has_dup

/-- Renames hypotheses with the same name.
-/
unsafe def dedup : tactic Unit :=
  (whenM has_dup) do
    let ctx ← local_context
    let n ← revert_lst ctx
    intron n
#align dedup dedup

end AddInteractive

namespace Tactic

-- Helper tactic for `mk_inj_eq
protected unsafe def apply_inj_lemma : tactic Unit := do
  let h ← intro `h
  let some (lhs, rhs) ← expr.is_eq <$> infer_type h
  let expr.const C _ ← return lhs.get_app_fn
  -- We disable auto_param and opt_param support to address issue #1943
      applyc
      (Name.mk_string "inj" C)
      { autoParam := ff
        optParam := ff }
  assumption
#align tactic.apply_inj_lemma tactic.apply_inj_lemma

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- Auxiliary tactic for proving `I.C.inj_eq` lemmas.
   These lemmas are automatically generated by the equation compiler.
   Example:
   ```
   list.cons.inj_eq : forall h1 h2 t1 t2, (h1::t1 = h2::t2) = (h1 = h2 ∧ t1 = t2) :=
   by mk_inj_eq
   ```
-/
unsafe def mk_inj_eq : tactic Unit :=
  sorry
#align tactic.mk_inj_eq tactic.mk_inj_eq

/-
     We use `_root_.*` in the following tactics because
     names are resolved at tactic execution time in interactive mode.
     See PR #1913

     TODO(Leo): This is probably not the only instance of this problem.
     `[ ... ] blocks are convenient to use because they allow us to use the interactive
     mode to write non interactive tactics.
     One potential fix for this issue is to resolve names in `[ ... ] at tactic
     compilation time.
     After this issue is fixed, we should remove the `_root_.*` workaround.
  -/
end Tactic

/-! Define inj_eq lemmas for inductive datatypes that were declared before `mk_inj_eq` -/


universe u v

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_inj_eq -/
theorem Sum.inl.inj_eq {α : Type u} (β : Type v) (a₁ a₂ : α) :
    (@Sum.inl α β a₁ = Sum.inl a₂) = (a₁ = a₂) := by
  run_tac
    tactic.mk_inj_eq
#align sum.inl.inj_eq Sum.inl.inj_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_inj_eq -/
theorem Sum.inr.inj_eq (α : Type u) {β : Type v} (b₁ b₂ : β) :
    (@Sum.inr α β b₁ = Sum.inr b₂) = (b₁ = b₂) := by
  run_tac
    tactic.mk_inj_eq
#align sum.inr.inj_eq Sum.inr.inj_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_inj_eq -/
theorem PSum.inl.inj_eq {α : Sort u} (β : Sort v) (a₁ a₂ : α) :
    (@PSum.inl α β a₁ = PSum.inl a₂) = (a₁ = a₂) := by
  run_tac
    tactic.mk_inj_eq
#align psum.inl.inj_eq PSum.inl.inj_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_inj_eq -/
theorem PSum.inr.inj_eq (α : Sort u) {β : Sort v} (b₁ b₂ : β) :
    (@PSum.inr α β b₁ = PSum.inr b₂) = (b₁ = b₂) := by
  run_tac
    tactic.mk_inj_eq
#align psum.inr.inj_eq PSum.inr.inj_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_inj_eq -/
theorem Sigma.mk.inj_eq {α : Type u} {β : α → Type v} (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) :
    (Sigma.mk a₁ b₁ = Sigma.mk a₂ b₂) = (a₁ = a₂ ∧ HEq b₁ b₂) := by
  run_tac
    tactic.mk_inj_eq
#align sigma.mk.inj_eq Sigma.mk.inj_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_inj_eq -/
theorem PSigma.mk.inj_eq {α : Sort u} {β : α → Sort v} (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) :
    (PSigma.mk a₁ b₁ = PSigma.mk a₂ b₂) = (a₁ = a₂ ∧ HEq b₁ b₂) := by
  run_tac
    tactic.mk_inj_eq
#align psigma.mk.inj_eq PSigma.mk.inj_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_inj_eq -/
theorem Subtype.mk.inj_eq {α : Sort u} {p : α → Prop} (a₁ : α) (h₁ : p a₁) (a₂ : α) (h₂ : p a₂) :
    (Subtype.mk a₁ h₁ = Subtype.mk a₂ h₂) = (a₁ = a₂) := by
  run_tac
    tactic.mk_inj_eq
#align subtype.mk.inj_eq Subtype.mk.inj_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_inj_eq -/
theorem Option.some.inj_eq {α : Type u} (a₁ a₂ : α) : (some a₁ = some a₂) = (a₁ = a₂) := by
  run_tac
    tactic.mk_inj_eq
#align option.some.inj_eq Option.some.inj_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_inj_eq -/
theorem List.cons.inj_eq {α : Type u} (h₁ : α) (t₁ : List α) (h₂ : α) (t₂ : List α) :
    (List.cons h₁ t₁ = List.cons h₂ t₂) = (h₁ = h₂ ∧ t₁ = t₂) := by
  run_tac
    tactic.mk_inj_eq
#align list.cons.inj_eq List.cons.inj_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_inj_eq -/
theorem Nat.succ.inj_eq (n₁ n₂ : Nat) : (Nat.succ n₁ = Nat.succ n₂) = (n₁ = n₂) := by
  run_tac
    tactic.mk_inj_eq
#align nat.succ.inj_eq Nat.succ.inj_eq

