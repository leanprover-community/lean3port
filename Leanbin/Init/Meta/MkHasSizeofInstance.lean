/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for constructing has_sizeof instance.
-/
prelude
import Leanbin.Init.Meta.RecUtil
import Leanbin.Init.Meta.ConstructorTactic

namespace Tactic

open Expr Environment List

-- Retrieve the name of the type we are building a has_sizeof instance for.
private unsafe def get_has_sizeof_type_name : tactic Name :=
  (do
      let app (const n ls) t ← target >>= whnf
      when (n ≠ `has_sizeof) failed
      let const I ls ← return (get_app_fn t)
      return I) <|>
    fail "mk_has_sizeof_instance tactic failed, target type is expected to be of the form (has_sizeof ...)"

-- Try to synthesize constructor argument using type class resolution
private unsafe def mk_has_sizeof_instance_for (a : expr) (use_default : Bool) : tactic expr := do
  let t ← infer_type a
  (do
        let m ← mk_app `has_sizeof [t]
        let inst ← mk_instance m
        mk_app `sizeof [t, inst, a]) <|>
      if use_default then return (const `nat.zero [])
      else do
        let f ← pp t
        fail
            (to_fmt "mk_has_sizeof_instance failed, failed to generate instance for" ++
              format.nest 2 (format.line ++ f))

private unsafe def mk_sizeof : Bool → Name → Name → List Name → Nat → tactic (List expr)
  | use_default, I_name, F_name, [], num_rec => return []
  | use_default, I_name, F_name, fname :: fnames, num_rec => do
    let field ← get_local fname
    let rec ← is_type_app_of field I_name
    let sz ← if rec then mk_brec_on_rec_value F_name num_rec else mk_has_sizeof_instance_for field use_default
    let szs ← mk_sizeof use_default I_name F_name fnames (if rec then num_rec + 1 else num_rec)
    return (sz :: szs)

private unsafe def mk_sum : List expr → expr
  | [] => app (const `nat.succ []) (const `nat.zero [])
  | e :: es => app (app (const `nat.add []) e) (mk_sum es)

private unsafe def has_sizeof_case (use_default : Bool) (I_name F_name : Name) (field_names : List Name) :
    tactic Unit := do
  let szs ← mk_sizeof use_default I_name F_name field_names 0
  exact (mk_sum szs)

private unsafe def for_each_has_sizeof_goal : Bool → Name → Name → List (List Name) → tactic Unit
  | d, I_name, F_name, [] => done <|> fail "mk_has_sizeof_instance failed, unexpected number of cases"
  | d, I_name, F_name, ns :: nss => do
    solve1 (has_sizeof_case d I_name F_name ns)
    for_each_has_sizeof_goal d I_name F_name nss

unsafe def mk_has_sizeof_instance_core (use_default : Bool) : tactic Unit := do
  let I_name ← get_has_sizeof_type_name
  constructor
  let env ← get_env
  let v_name : Name ← return `_v
  let F_name : Name ← return `_F
  let num_indices := inductive_num_indices env I_name
  let idx_names :=
    List.map (fun p : Name × Nat => mkNumName p.fst p.snd)
      (List.zipₓ (List.repeat `idx num_indices) (List.iota num_indices))
  -- Use brec_on if type is recursive.
      -- We store the functional in the variable F.
      if is_recursive env I_name then
      intro `_v >>= fun x =>
        induction x (idx_names ++ [v_name, F_name]) (some <| mkStrName I_name "brec_on") >> return ()
    else intro v_name >> return ()
  let arg_names : List (List Name) ← mk_constructors_arg_names I_name `_p
  get_local v_name >>= fun v => cases v (join arg_names)
  for_each_has_sizeof_goal use_default I_name F_name arg_names

unsafe def mk_has_sizeof_instance : tactic Unit :=
  mk_has_sizeof_instance_core false

end Tactic

