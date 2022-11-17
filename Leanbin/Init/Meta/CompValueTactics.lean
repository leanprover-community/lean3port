/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Data.Option.Basic

unsafe axiom mk_nat_val_ne_proof : expr → expr → Option expr
#align mk_nat_val_ne_proof mk_nat_val_ne_proof

unsafe axiom mk_nat_val_lt_proof : expr → expr → Option expr
#align mk_nat_val_lt_proof mk_nat_val_lt_proof

unsafe axiom mk_nat_val_le_proof : expr → expr → Option expr
#align mk_nat_val_le_proof mk_nat_val_le_proof

unsafe axiom mk_fin_val_ne_proof : expr → expr → Option expr
#align mk_fin_val_ne_proof mk_fin_val_ne_proof

unsafe axiom mk_char_val_ne_proof : expr → expr → Option expr
#align mk_char_val_ne_proof mk_char_val_ne_proof

unsafe axiom mk_string_val_ne_proof : expr → expr → Option expr
#align mk_string_val_ne_proof mk_string_val_ne_proof

unsafe axiom mk_int_val_ne_proof : expr → expr → Option expr
#align mk_int_val_ne_proof mk_int_val_ne_proof

namespace Tactic

open Expr

unsafe def comp_val : tactic Unit := do
  let t ← target >>= instantiate_mvars
  guard (is_app t)
  let type ← infer_type t.app_arg
  (do
        is_def_eq type (const `nat [])
        (do
              let (a, b) ← is_ne t
              let pr ← mk_nat_val_ne_proof a b
              exact pr) <|>
            (do
                let (a, b) ← is_lt t
                let pr ← mk_nat_val_lt_proof a b
                exact pr) <|>
              (do
                  let (a, b) ← is_gt t
                  let pr ← mk_nat_val_lt_proof b a
                  exact pr) <|>
                (do
                    let (a, b) ← is_le t
                    let pr ← mk_nat_val_le_proof a b
                    exact pr) <|>
                  do
                  let (a, b) ← is_ge t
                  let pr ← mk_nat_val_le_proof b a
                  exact pr) <|>
      (do
          is_def_eq type (const `char [])
          let (a, b) ← is_ne t
          let pr ← mk_char_val_ne_proof a b
          exact pr) <|>
        (do
            is_def_eq type (const `string [])
            let (a, b) ← is_ne t
            let pr ← mk_string_val_ne_proof a b
            exact pr) <|>
          (do
              is_def_eq type (const `int [])
              let (a, b) ← is_ne t
              let pr ← mk_int_val_ne_proof a b
              exact pr) <|>
            (do
                let type ← whnf type
                guard (type = q(@Subtype Nat))
                applyc `subtype.ne_of_val_ne
                let (q(Subtype.mk $(a) $(ha)), q(Subtype.mk $(b) $(hb))) ← is_ne t
                let pr ← mk_nat_val_ne_proof a b
                exact pr) <|>
              (do
                  let type ← whnf type
                  guard (type = q(@Fin))
                  applyc `` Fin.ne_of_vne
                  let (q(Fin.mk $(a) $(ha)), q(Fin.mk $(b) $(hb))) ← is_ne t
                  let pr ← mk_nat_val_ne_proof a b
                  exact pr) <|>
                do
                let (a, b) ← is_eq t
                unify a b
                to_expr ``(Eq.refl $(a)) >>= exact
#align tactic.comp_val tactic.comp_val

end Tactic

namespace Tactic

namespace Interactive

/-- Close goals of the form `n ≠ m` when `n` and `m` have type `nat`, `char`, `string`, `int` or
    subtypes `{i : ℕ // p i}`, and they are literals.
    It also closes goals of the form `n < m`, `n > m`, `n ≤ m` and `n ≥ m` for `nat`.
    If the goal is of the form `n = m`, then it tries to close it using reflexivity. -/
unsafe def comp_val :=
  tactic.comp_val
#align tactic.interactive.comp_val tactic.interactive.comp_val

end Interactive

end Tactic

