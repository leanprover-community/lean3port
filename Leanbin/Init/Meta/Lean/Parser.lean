/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.HasReflect
import Leanbin.Init.Control.Alternative

namespace Lean

-- TODO: make inspectable (and pure)
unsafe axiom parser_state : Type
#align lean.parser_state lean.parser_state

unsafe axiom parser_state.env : parser_state → environment
#align lean.parser_state.env lean.parser_state.env

unsafe axiom parser_state.options : parser_state → options
#align lean.parser_state.options lean.parser_state.options

unsafe axiom parser_state.cur_pos : parser_state → Pos
#align lean.parser_state.cur_pos lean.parser_state.cur_pos

@[reducible]
unsafe def parser :=
  interaction_monad parser_state
#align lean.parser lean.parser

@[reducible]
unsafe def parser_result :=
  interaction_monad.result parser_state
#align lean.parser_result lean.parser_result

open InteractionMonad

open InteractionMonad.Result

namespace Parser

variable {α : Type}

unsafe def val (p : lean.parser (reflected_value α)) : lean.parser α :=
  reflected_value.val <$> p
#align lean.parser.val lean.parser.val

protected unsafe class reflectable (p : parser α) where
  full : parser (reflected_value α)
#align lean.parser.reflectable lean.parser.reflectable

namespace Reflectable

unsafe def expr {p : parser α} (r : reflectable p) : parser expr :=
  reflected_value.expr <$> r.full
#align lean.parser.reflectable.expr lean.parser.reflectable.expr

unsafe def to_parser {p : parser α} (r : reflectable p) : parser α :=
  val r.full
#align lean.parser.reflectable.to_parser lean.parser.reflectable.to_parser

end Reflectable

unsafe def get_env : parser environment := fun s => success s.env s
#align lean.parser.get_env lean.parser.get_env

unsafe axiom set_env : environment → parser Unit
#align lean.parser.set_env lean.parser.set_env

/-- Make sure the next token is an identifier, consume it, and
    produce the quoted name `t, where t is the identifier. -/
unsafe axiom ident : parser Name
#align lean.parser.ident lean.parser.ident

/-- Make sure the next token is a small nat, consume it, and produce it -/
unsafe axiom small_nat : parser Nat
#align lean.parser.small_nat lean.parser.small_nat

/-- Check that the next token is `tk` and consume it. `tk` must be a registered token. -/
unsafe axiom tk (tk : String) : parser Unit
#align lean.parser.tk lean.parser.tk

/-- Parse an unelaborated expression using the given right-binding power.
When `pat := tt`, the expression is parsed as a pattern, i.e. local
constants are not checked. -/
protected unsafe axiom pexpr (rbp := Std.Prec.max) (pat := false) : parser pexpr
#align lean.parser.pexpr lean.parser.pexpr

/-- a variable to local scope -/
unsafe axiom add_local (v : expr) : parser Unit
#align lean.parser.add_local lean.parser.add_local

unsafe axiom add_local_level (v : Name) : parser Unit
#align lean.parser.add_local_level lean.parser.add_local_level

unsafe axiom list_include_var_names : parser (List Name)
#align lean.parser.list_include_var_names lean.parser.list_include_var_names

unsafe axiom list_available_include_vars : parser (List expr)
#align lean.parser.list_available_include_vars lean.parser.list_available_include_vars

unsafe axiom include_var : Name → parser Unit
#align lean.parser.include_var lean.parser.include_var

unsafe axiom omit_var : Name → parser Unit
#align lean.parser.omit_var lean.parser.omit_var

unsafe axiom push_local_scope : parser Unit
#align lean.parser.push_local_scope lean.parser.push_local_scope

unsafe axiom pop_local_scope : parser Unit
#align lean.parser.pop_local_scope lean.parser.pop_local_scope

/-- Run the parser in a local declaration scope.

Local declarations added via `add_local` do not propagate outside of this scope.
-/
@[inline]
unsafe def with_local_scope {α} (p : parser α) : parser α :=
  interaction_monad.bracket push_local_scope p pop_local_scope
#align lean.parser.with_local_scope lean.parser.with_local_scope

protected unsafe axiom itactic_reflected : parser (reflected_value (tactic Unit))
#align lean.parser.itactic_reflected lean.parser.itactic_reflected

/-- Parse an interactive tactic block: `begin` .. `end` -/
@[reducible]
protected unsafe def itactic : parser (tactic Unit) :=
  val parser.itactic_reflected
#align lean.parser.itactic lean.parser.itactic

/-- Do not report info from content parsed by `p`. -/
unsafe axiom skip_info (p : parser α) : parser α
#align lean.parser.skip_info lean.parser.skip_info

/-- Set goal info position of content parsed by `p` to current position. Nested calls take precedence. -/
unsafe axiom set_goal_info_pos (p : parser α) : parser α
#align lean.parser.set_goal_info_pos lean.parser.set_goal_info_pos

/-- Return the current parser position without consuming any input. -/
unsafe def cur_pos : parser Pos := fun s => success (parser_state.cur_pos s) s
#align lean.parser.cur_pos lean.parser.cur_pos

/-- Temporarily replace input of the parser state, run `p`, and return remaining input. -/
unsafe axiom with_input (p : parser α) (input : String) : parser (α × String)
#align lean.parser.with_input lean.parser.with_input

/-- Parse a top-level command. -/
unsafe axiom command_like : parser Unit
#align lean.parser.command_like lean.parser.command_like

unsafe def parser_orelse (p₁ p₂ : parser α) : parser α := fun s =>
  let pos₁ := parser_state.cur_pos s
  result.cases_on (p₁ s) success fun e₁ ref₁ s' =>
    let pos₂ := parser_state.cur_pos s'
    if pos₁ ≠ pos₂ then exception e₁ ref₁ s' else result.cases_on (p₂ s) success exception
#align lean.parser.parser_orelse lean.parser.parser_orelse

unsafe instance : Alternative parser :=
  { interaction_monad.monad with failure := @interaction_monad.failed _, orelse := @parser_orelse }

-- TODO: move
unsafe def many.{u, v} {f : Type u → Type v} [Monad f] [Alternative f] {a : Type u} : f a → f (List a)
  | x =>
    (do
        let y ← x
        let ys ← many x
        return $ y :: ys) <|>
      pure List.nil
#align lean.parser.many lean.parser.many

-- mathport name: «expr ?»
local postfix:100 "?" => optional

-- mathport name: «expr *»
local postfix:100 "*" => many

unsafe def sep_by : parser Unit → parser α → parser (List α)
  | s, p => List.cons <$> p <*> (s *> p)* <|> return []
#align lean.parser.sep_by lean.parser.sep_by

unsafe axiom of_tactic : tactic α → parser α
#align lean.parser.of_tactic lean.parser.of_tactic

unsafe instance : Coe (tactic α) (parser α) :=
  ⟨of_tactic⟩

namespace Reflectable

unsafe instance cast (p : lean.parser (reflected_value α)) : reflectable (val p) where full := p
#align lean.parser.reflectable.cast lean.parser.reflectable.cast

unsafe instance has_reflect [r : has_reflect α] (p : lean.parser α) :
    reflectable p where full := do
    let rp ← p
    return ⟨rp⟩
#align lean.parser.reflectable.has_reflect lean.parser.reflectable.has_reflect

unsafe instance optional {α : Type} [reflected _ α] (p : parser α) [r : reflectable p] :
    reflectable (optional p) where full := reflected_value.subst some <$> r.full <|> return ⟨none⟩
#align lean.parser.reflectable.optional lean.parser.reflectable.optional

end Reflectable

unsafe def reflect (p : parser α) [r : reflectable p] : parser expr :=
  r.expr
#align lean.parser.reflect lean.parser.reflect

unsafe axiom run {α} : parser α → tactic α
#align lean.parser.run lean.parser.run

unsafe def run_with_input {α} : parser α → String → tactic α := fun p s => Prod.fst <$> run (with_input p s)
#align lean.parser.run_with_input lean.parser.run_with_input

end Parser

end Lean

