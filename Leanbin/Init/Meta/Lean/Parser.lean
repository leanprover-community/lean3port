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

unsafe axiom parser_state.env : parser_state → environment

unsafe axiom parser_state.options : parser_state → options

unsafe axiom parser_state.cur_pos : parser_state → Pos

@[reducible]
unsafe def parser :=
  interaction_monad parser_state

@[reducible]
unsafe def parser_result :=
  interaction_monad.result parser_state

open InteractionMonad

open InteractionMonad.Result

namespace Parser

variable {α : Type}

unsafe def val (p : lean.parser (reflected_value α)) : lean.parser α :=
  reflected_value.val <$> p

protected unsafe class reflectable (p : parser α) where
  full : parser (reflected_value α)

namespace Reflectable

unsafe def expr {p : parser α} (r : reflectable p) : parser expr :=
  reflected_value.expr <$> r.full

unsafe def to_parser {p : parser α} (r : reflectable p) : parser α :=
  val r.full

end Reflectable

unsafe def get_env : parser environment := fun s => success s.env s

unsafe axiom set_env : environment → parser Unit

/-- Make sure the next token is an identifier, consume it, and
    produce the quoted name `t, where t is the identifier. -/
unsafe axiom ident : parser Name

/-- Make sure the next token is a small nat, consume it, and produce it -/
unsafe axiom small_nat : parser Nat

/-- Check that the next token is `tk` and consume it. `tk` must be a registered token. -/
unsafe axiom tk (tk : Stringₓ) : parser Unit

/-- Parse an unelaborated expression using the given right-binding power.
When `pat := tt`, the expression is parsed as a pattern, i.e. local
constants are not checked. -/
protected unsafe axiom pexpr (rbp := Std.Prec.max) (pat := false) : parser pexpr

/-- a variable to local scope -/
unsafe axiom add_local (v : expr) : parser Unit

unsafe axiom add_local_level (v : Name) : parser Unit

unsafe axiom list_include_var_names : parser (List Name)

unsafe axiom list_available_include_vars : parser (List expr)

unsafe axiom include_var : Name → parser Unit

unsafe axiom omit_var : Name → parser Unit

unsafe axiom push_local_scope : parser Unit

unsafe axiom pop_local_scope : parser Unit

/-- Run the parser in a local declaration scope.

Local declarations added via `add_local` do not propagate outside of this scope.
-/
@[inline]
unsafe def with_local_scope {α} (p : parser α) : parser α :=
  interaction_monad.bracket push_local_scope p pop_local_scope

protected unsafe axiom itactic_reflected : parser (reflected_value (tactic Unit))

/-- Parse an interactive tactic block: `begin` .. `end` -/
@[reducible]
protected unsafe def itactic : parser (tactic Unit) :=
  val parser.itactic_reflected

/-- Do not report info from content parsed by `p`. -/
unsafe axiom skip_info (p : parser α) : parser α

/-- Set goal info position of content parsed by `p` to current position. Nested calls take precedence. -/
unsafe axiom set_goal_info_pos (p : parser α) : parser α

/-- Return the current parser position without consuming any input. -/
unsafe def cur_pos : parser Pos := fun s => success (parser_state.cur_pos s) s

/-- Temporarily replace input of the parser state, run `p`, and return remaining input. -/
unsafe axiom with_input (p : parser α) (input : Stringₓ) : parser (α × Stringₓ)

/-- Parse a top-level command. -/
unsafe axiom command_like : parser Unit

unsafe def parser_orelse (p₁ p₂ : parser α) : parser α := fun s =>
  let pos₁ := parser_state.cur_pos s
  result.cases_on (p₁ s) success fun e₁ ref₁ s' =>
    let pos₂ := parser_state.cur_pos s'
    if pos₁ ≠ pos₂ then exception e₁ ref₁ s' else result.cases_on (p₂ s) success exception

unsafe instance : Alternativeₓ parser :=
  { interaction_monad.monad with failure := @interaction_monad.failed _, orelse := @parser_orelse }

-- TODO: move
unsafe def many.{u, v} {f : Type u → Type v} [Monadₓ f] [Alternativeₓ f] {a : Type u} : f a → f (List a)
  | x =>
    (do
        let y ← x
        let ys ← many x
        return <| y :: ys) <|>
      pure List.nil

-- mathport name: «expr ?»
local postfix:100 "?" => optionalₓ

-- mathport name: «expr *»
local postfix:100 "*" => many

unsafe def sep_by : parser Unit → parser α → parser (List α)
  | s, p => List.cons <$> p <*> (s *> p)* <|> return []

unsafe axiom of_tactic : tactic α → parser α

unsafe instance : Coe (tactic α) (parser α) :=
  ⟨of_tactic⟩

namespace Reflectable

unsafe instance cast (p : lean.parser (reflected_value α)) : reflectable (val p) where full := p

unsafe instance has_reflect [r : has_reflect α] (p : lean.parser α) :
    reflectable p where full := do
    let rp ← p
    return ⟨rp⟩

unsafe instance optional {α : Type} [reflected _ α] (p : parser α) [r : reflectable p] :
    reflectable (optionalₓ p) where full := reflected_value.subst some <$> r.full <|> return ⟨none⟩

end Reflectable

unsafe def reflect (p : parser α) [r : reflectable p] : parser expr :=
  r.expr

unsafe axiom run {α} : parser α → tactic α

unsafe def run_with_input {α} : parser α → Stringₓ → tactic α := fun p s => Prod.fst <$> run (with_input p s)

end Parser

end Lean

