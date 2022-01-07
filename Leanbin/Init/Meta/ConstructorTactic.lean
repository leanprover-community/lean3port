prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Function

namespace Tactic

private unsafe def target' : tactic expr :=
  target >>= instantiate_mvars >>= whnf

unsafe def get_constructors_for (e : expr) : tactic (List Name) := do
  let env ← get_env
  let I ← return e.extract_opt_auto_param.get_app_fn.const_name
  when (¬env.is_inductive I) (fail "constructor tactic failed, target is not an inductive datatype")
  return $ env.constructors_of I

private unsafe def try_constructors (cfg : apply_cfg) : List Name → tactic (List (Name × expr))
  | [] => fail "constructor tactic failed, none of the constructors is applicable"
  | c :: cs => (mk_const c >>= fun e => apply e cfg) <|> try_constructors cs

unsafe def constructor (cfg : apply_cfg := {  }) : tactic (List (Name × expr)) :=
  target' >>= get_constructors_for >>= try_constructors cfg

unsafe def econstructor : tactic (List (Name × expr)) :=
  constructor { NewGoals := new_goals.non_dep_only }

unsafe def fconstructor : tactic (List (Name × expr)) :=
  constructor { NewGoals := new_goals.all }

unsafe def left : tactic (List (Name × expr)) := do
  let tgt ← target'
  let [c₁, c₂] ← get_constructors_for tgt |
    fail "left tactic failed, target is not an inductive datatype with two constructors"
  mk_const c₁ >>= apply

unsafe def right : tactic (List (Name × expr)) := do
  let tgt ← target'
  let [c₁, c₂] ← get_constructors_for tgt |
    fail "left tactic failed, target is not an inductive datatype with two constructors"
  mk_const c₂ >>= apply

unsafe def constructor_idx (idx : Nat) : tactic (List (Name × expr)) := do
  let cs ← target' >>= get_constructors_for
  let some c ← return $ cs.nth (idx - 1) |
    fail "constructor_idx tactic failed, target is an inductive datatype, but it does not have sufficient constructors"
  mk_const c >>= apply

unsafe def split : tactic (List (Name × expr)) := do
  let [c] ← target' >>= get_constructors_for |
    fail "split tactic failed, target is not an inductive datatype with only one constructor"
  mk_const c >>= apply

open Expr

private unsafe def apply_num_metavars : expr → expr → Nat → tactic expr
  | f, ftype, 0 => return f
  | f, ftype, n + 1 => do
    let pi m bi d b ← whnf ftype
    let a ← mk_meta_var d
    let new_f ← return $ f a
    let new_ftype ← return $ b.instantiate_var a
    apply_num_metavars new_f new_ftype n

unsafe def existsi (e : expr) : tactic Unit := do
  let [c] ← target' >>= get_constructors_for |
    fail "existsi tactic failed, target is not an inductive datatype with only one constructor"
  let fn ← mk_const c
  let fn_type ← infer_type fn
  let n ← get_arity fn
  when (n < 2) (fail "existsi tactic failed, constructor must have at least two arguments")
  let t ← apply_num_metavars fn fn_type (n - 2)
  eapply (app t e)
  let t_type ← infer_type t >>= whnf
  let e_type ← infer_type e
  guardₓ t_type.is_pi <|> fail "existsi tactic failed, failed to infer type"
  unify t_type.binding_domain e_type <|>
      fail "existsi tactic failed, type mismatch between given term witness and expected type"

end Tactic

