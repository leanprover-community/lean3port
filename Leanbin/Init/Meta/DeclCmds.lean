/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.RbMap

open Tactic

open Native

private unsafe def apply_replacement (replacements : name_map Name) (e : expr) : expr :=
  e.replace fun e d =>
    match e with
    | expr.const n ls =>
      match replacements.find n with
      | some new_n => some (expr.const new_n ls)
      | none => none
    | _ => none

/-- Given a set of constant renamings `replacements` and a declaration name `src_decl_name`, create a new
   declaration called `new_decl_name` s.t. its type is the type of `src_decl_name` after applying the
   given constant replacement.

   Remark: the new type must be definitionally equal to the type of `src_decl_name`.

   Example:
   Assume the environment contains
        def f : nat -> nat  := ...
        def g : nat -> nat  := f
        lemma f_lemma : forall a, f a > 0 := ...

   Moreover, assume we have a mapping M containing `f -> `g
   Then, the command
        run_command copy_decl_updating_type M `f_lemma `g_lemma
   creates the declaration
        lemma g_lemma : forall a, g a > 0 := ... -/
unsafe def copy_decl_updating_type (replacements : name_map Name) (src_decl_name : Name) (new_decl_name : Name) :
    Tactic Unit := do
  let env ← get_env
  let decl ← env.get src_decl_name
  let decl := decl.update_name <| new_decl_name
  let decl := decl.update_type <| apply_replacement replacements decl.type
  let decl := decl.update_value <| expr.const src_decl_name (decl.univ_params.map level.param)
  add_decl decl

unsafe def copy_decl_using (replacements : name_map Name) (src_decl_name : Name) (new_decl_name : Name) : Tactic Unit :=
  do
  let env ← get_env
  let decl ← env.get src_decl_name
  let decl := decl.update_name <| new_decl_name
  let decl := decl.update_type <| apply_replacement replacements decl.type
  let decl := decl.map_value <| apply_replacement replacements
  add_decl decl

