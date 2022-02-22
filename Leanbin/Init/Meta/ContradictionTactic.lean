/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Function

namespace Tactic

open Expr Tactic Decidable Environment

private unsafe def contra_p_not_p : List expr → List expr → tactic Unit
  | [], Hs => failed
  | H1 :: Rs, Hs => do
    let t ← extract_opt_auto_param <$> infer_type H1 >>= whnf
    (do
          let a ← match_not t
          let H2 ← find_same_type a Hs
          let tgt ← target
          let pr ← mk_app `absurd [tgt, H2, H1]
          exact pr) <|>
        contra_p_not_p Rs Hs

private unsafe def contra_false : List expr → tactic Unit
  | [] => failed
  | H :: Hs => do
    let t ← extract_opt_auto_param <$> infer_type H
    if is_false t then do
        let tgt ← target
        let pr ← mk_app `false.rec [tgt, H]
        exact pr
      else contra_false Hs

private unsafe def contra_not_a_refl_rel_a : List expr → tactic Unit
  | [] => failed
  | H :: Hs => do
    let t ← extract_opt_auto_param <$> infer_type H >>= head_beta
    (do
          let (lhs, rhs) ← match_ne t
          unify lhs rhs
          let tgt ← target
          let refl_pr ← mk_app `eq.refl [lhs]
          mk_app `absurd [tgt, refl_pr, H] >>= exact) <|>
        (do
            let p ← match_not t
            let (refl_lemma, lhs, rhs) ← match_refl_app p
            unify lhs rhs
            let tgt ← target
            let refl_pr ← mk_app refl_lemma [lhs]
            mk_app `absurd [tgt, refl_pr, H] >>= exact) <|>
          contra_not_a_refl_rel_a Hs

private unsafe def contra_constructor_eq : List expr → tactic Unit
  | [] => failed
  | H :: Hs => do
    let t ← extract_opt_auto_param <$> infer_type H >>= whnf
    match t with
      | quote.1 ((%%ₓlhs_0 : %%ₓα) = %%ₓrhs_0) => do
        let env ← get_env
        let lhs ← whnf lhs_0
        let rhs ← whnf rhs_0
        if
              is_constructor_app env lhs ∧
                is_constructor_app env rhs ∧ const_name (get_app_fn lhs) ≠ const_name (get_app_fn rhs) then
            do
            let tgt ← target
            let I_name ← return <| Name.getPrefix (const_name (get_app_fn lhs))
            let pr ← mk_app (mkStrName I_name "no_confusion") [tgt, lhs, rhs, H]
            exact pr
          else contra_constructor_eq Hs
      | _ => contra_constructor_eq Hs

unsafe def contradiction : tactic Unit := do
  try intro1
  let ctx ← local_context
  contra_false ctx <|>
      contra_not_a_refl_rel_a ctx <|>
        contra_p_not_p ctx ctx <|> contra_constructor_eq ctx <|> fail "contradiction tactic failed"

unsafe def exfalso : tactic Unit := do
  fail_if_no_goals
  assert `Hfalse (expr.const `false [])
  swap
  contradiction

end Tactic

