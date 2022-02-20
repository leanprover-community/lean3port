/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for showing that a type has decidable equality.
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Data.Option.Basic

namespace Tactic

open Expr

/-- Return tt iff e's type is of the form `(I_name ...)` -/
unsafe def is_type_app_of (e : expr) (I_name : Name) : tactic Bool := do
  let t ← infer_type e
  return <| is_constant_of (get_app_fn t) I_name

/-- Auxiliary function for using brec_on "dictionary" -/
private unsafe def mk_rec_inst_aux : expr → Nat → tactic expr
  | F, 0 => do
    let P ← mk_app `pprod.fst [F]
    mk_app `pprod.fst [P]
  | F, n + 1 => do
    let F' ← mk_app `pprod.snd [F]
    mk_rec_inst_aux F' n

/-- Construct brec_on "recursive value". F_name is the name of the brec_on "dictionary".
   Type of the F_name hypothesis should be of the form (below (C ...)) where C is a constructor.
   The result is the "recursive value" for the (i+1)-th recursive value of the constructor C. -/
unsafe def mk_brec_on_rec_value (F_name : Name) (i : Nat) : tactic expr := do
  let F ← get_local F_name
  mk_rec_inst_aux F i

unsafe def constructor_num_fields (c : Name) : tactic Nat := do
  let env ← get_env
  let decl ← env.get c
  let ctype ← return decl.type
  let arity ← get_pi_arity ctype
  let I ← env.inductive_type_of c
  let nparams ← return (env.inductive_num_params I)
  return <| arity - nparams

private unsafe def mk_name_list_aux : Name → Nat → Nat → List Name → List Name × Nat
  | p, i, 0, l => (List.reverse l, i)
  | p, i, j + 1, l => mk_name_list_aux p (i + 1) j (mkNumName p i :: l)

private unsafe def mk_name_list (p : Name) (i : Nat) (n : Nat) : List Name × Nat :=
  mk_name_list_aux p i n []

/-- Return a list of names of the form [p.i, ..., p.{i+n}] where n is
   the number of fields of the constructor c -/
unsafe def mk_constructor_arg_names (c : Name) (p : Name) (i : Nat) : tactic (List Name × Nat) := do
  let nfields ← constructor_num_fields c
  return <| mk_name_list p i nfields

private unsafe def mk_constructors_arg_names_aux : List Name → Name → Nat → List (List Name) → tactic (List (List Name))
  | [], p, i, r => return (List.reverse r)
  | c :: cs, p, i, r => do
    let v : List Name × Nat ← mk_constructor_arg_names c p i
    match v with
      | (l, i') => mk_constructors_arg_names_aux cs p i' (l :: r)

/-- Given an inductive datatype I with k constructors and where constructor i has n_i fields,
   return the list [[p.1, ..., p.n_1], [p.{n_1 + 1}, ..., p.{n_1 + n_2}], ..., [..., p.{n_1 + ... + n_k}]] -/
unsafe def mk_constructors_arg_names (I : Name) (p : Name) : tactic (List (List Name)) := do
  let env ← get_env
  let cs ← return <| env.constructors_of I
  mk_constructors_arg_names_aux cs p 1 []

private unsafe def mk_fresh_arg_name_aux : Name → Nat → name_set → tactic (Name × name_set)
  | n, i, s => do
    let r ← get_unused_name n (some i)
    if s r then mk_fresh_arg_name_aux n (i + 1) s else return (r, s r)

private unsafe def mk_fresh_arg_name (n : Name) (s : name_set) : tactic (Name × name_set) := do
  let r ← get_unused_name n
  if s r then mk_fresh_arg_name_aux n 1 s else return (r, s r)

private unsafe def mk_constructor_fresh_names_aux : Nat → expr → name_set → tactic (List Name × name_set)
  | nparams, ty, s => do
    let ty ← whnf ty
    match ty with
      | expr.pi n bi d b =>
        if nparams = 0 then do
          let (n', s') ← mk_fresh_arg_name n s
          let x ← mk_local' n' bi d
          let ty' := b x
          let (ns, s'') ← mk_constructor_fresh_names_aux 0 ty' s'
          return (n' :: ns, s'')
        else do
          let x ← mk_local' n bi d
          let ty' := b x
          mk_constructor_fresh_names_aux (nparams - 1) ty' s
      | _ => return ([], s)

unsafe def mk_constructor_fresh_names (nparams : Nat) (c : Name) (s : name_set) : tactic (List Name × name_set) := do
  let d ← get_decl c
  let t := d.type
  mk_constructor_fresh_names_aux nparams t s

private unsafe def mk_constructors_fresh_names_aux :
    Nat → List Name → name_set → List (List Name) → tactic (List (List Name))
  | np, [], s, r => return (List.reverse r)
  | np, c :: cs, s, r => do
    let (ns, s') ← mk_constructor_fresh_names np c s
    mk_constructors_fresh_names_aux np cs s' (ns :: r)

unsafe def mk_constructors_fresh_names (I : Name) : tactic (List (List Name)) := do
  let env ← get_env
  let cs := env.constructors_of I
  let nparams := env.inductive_num_params I
  mk_constructors_fresh_names_aux nparams cs mk_name_set []

end Tactic

