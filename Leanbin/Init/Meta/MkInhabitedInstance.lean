/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for showing that a type is inhabited.
-/
prelude
import Init.Meta.InteractiveBase
import Init.Meta.ContradictionTactic
import Init.Meta.ConstructorTactic
import Init.Meta.InjectionTactic
import Init.Meta.RelationTactics

#align_import init.meta.mk_inhabited_instance from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

namespace Tactic

open Expr Environment List

/-- Retrieve the name of the type we are building an inhabitant instance for. -/
private unsafe def get_inhabited_type_name : tactic Name :=
  (do
      let app (const n ls) t ← target >>= whnf
      when (n ≠ `inhabited) failed
      let const I ls ← return (get_app_fn t)
      return I) <|>
    fail
      "mk_inhabited_instance tactic failed, target type is expected to be of the form (inhabited ...)"

/-- Try to synthesize constructor argument using type class resolution -/
private unsafe def mk_inhabited_arg : tactic Unit := do
  let tgt ← target
  let inh ← mk_app `inhabited [tgt]
  let inst ← mk_instance inh
  mk_app `inhabited.default [inst] >>= exact

private unsafe def try_constructors : Nat → Nat → tactic Unit
  | 0, n => failed
  | i + 1, n =>
    (do
        constructor_idx (n - i)
        all_goals mk_inhabited_arg
        done) <|>
      try_constructors i n

unsafe def mk_inhabited_instance : tactic Unit := do
  let I ← get_inhabited_type_name
  let env ← get_env
  let n := length (constructors_of env I)
  when (n = 0) (fail f! "mk_inhabited_instance failed, type '{I}' does not have constructors")
  constructor
  try_constructors n n <|>
      fail
        f! "mk_inhabited_instance failed, failed to build instance using all constructors of '{I}'"
#align tactic.mk_inhabited_instance tactic.mk_inhabited_instance

end Tactic

