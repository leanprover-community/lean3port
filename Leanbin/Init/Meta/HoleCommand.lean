/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Tactic

/-- The front-end (e.g., Emacs, VS Code) can invoke commands for holes `{! ... !}` in
a declaration. A command is a tactic that takes zero or more pre-terms in the
hole, and returns a list of pair (s, descr) where 's' is a substitution and 'descr' is
a short explanation for the substitution.
Each string 's' represents a different way to fill the hole.
The front-end is responsible for replacing the hole with the string/alternative selected by the user.

This infra-structure can be use to implement auto-fill and/or refine commands.

An action may return an empty list. This is useful for actions that just return
information such as: the type of an expression, its normal form, etc.
-/
unsafe structure hole_command where
  Name : Stringₓ
  descr : Stringₓ
  action : List pexpr → tactic (List (Stringₓ × Stringₓ))

open Tactic

@[hole_command]
unsafe def infer_type_cmd : hole_command where
  Name := "Infer"
  descr := "Infer type of the expression in the hole"
  action := fun ps => do
    let [p] ← return ps | fail "Infer command failed, the hole must contain a single term"
    let e ← to_expr p
    let t ← infer_type e
    trace t
    return []

@[hole_command]
unsafe def show_goal_cmd : hole_command where
  Name := "Show"
  descr := "Show the current goal"
  action := fun _ => do
    trace_state
    return []

@[hole_command]
unsafe def use_cmd : hole_command where
  Name := "Use"
  descr := "Try to fill the hole using the given argument"
  action := fun ps => do
    let [p] ← return ps | fail "Use command failed, the hole must contain a single term"
    let t ← target
    let e ← to_expr (pquote.1 (%%ₓp : %%ₓt))
    let ty ← infer_type e
    is_def_eq t ty
    let fmt ← tactic_format_expr e
    let o ← get_options
    let s := fmt.toString o
    return [(s, "")]

