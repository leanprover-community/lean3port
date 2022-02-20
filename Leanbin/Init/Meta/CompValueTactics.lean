/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Data.Option.Basic

unsafe axiom mk_nat_val_ne_proof : expr → expr → Option expr

unsafe axiom mk_nat_val_lt_proof : expr → expr → Option expr

unsafe axiom mk_nat_val_le_proof : expr → expr → Option expr

unsafe axiom mk_fin_val_ne_proof : expr → expr → Option expr

unsafe axiom mk_char_val_ne_proof : expr → expr → Option expr

unsafe axiom mk_string_val_ne_proof : expr → expr → Option expr

unsafe axiom mk_int_val_ne_proof : expr → expr → Option expr

namespace Tactic

open Expr

unsafe def comp_val : tactic Unit := do
  let t ← target >>= instantiate_mvars
  guardₓ (is_app t)
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
                guardₓ (type = quote.1 (@Subtype Nat))
                applyc `subtype.ne_of_val_ne
                let (quote.1 (Subtype.mk (%%ₓa) (%%ₓha)), quote.1 (Subtype.mk (%%ₓb) (%%ₓhb))) ← is_ne t
                let pr ← mk_nat_val_ne_proof a b
                exact pr) <|>
              do
              let (a, b) ← is_eq t
              unify a b
              to_expr (pquote.1 (Eq.refl (%%ₓa))) >>= exact

end Tactic

namespace Tactic

namespace Interactive

/-- Close goals of the form `n ≠ m` when `n` and `m` have type `nat`, `char`, `string`, `int` or
    subtypes `{i : ℕ // p i}`, and they are literals.
    It also closes goals of the form `n < m`, `n > m`, `n ≤ m` and `n ≥ m` for `nat`.
    If the goal is of the form `n = m`, then it tries to close it using reflexivity. -/
unsafe def comp_val :=
  tactic.comp_val

end Interactive

end Tactic

