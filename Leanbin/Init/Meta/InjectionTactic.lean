prelude
import Leanbin.Init.Meta.Tactic

namespace Tactic

open Expr

unsafe def injection_with (h : expr) (ns : List Name) (base := `h) (offset := some 1) :
    tactic (List expr × List Name) := do
  let H ← infer_type h
  let (lhs, rhs, constructor_left, constructor_right, inj_name) ←
    (do
          let (lhs, rhs) ← match_eq H
          let lhs ← whnf_ginductive lhs
          let rhs ← whnf_ginductive rhs
          let env ← get_env
          let const constructor_left _ ← pure $ get_app_fn lhs
          let const constructor_right _ ← pure $ get_app_fn rhs
          let inj_name ← resolve_constant $ constructor_left ++ "inj_arrow"
          pure (lhs, rhs, constructor_left, constructor_right, inj_name)) <|>
        fail
          "injection tactic failed, argument must be an equality proof where lhs and rhs are of the form (c ...), where c is a constructor"
  if constructor_left = constructor_right then do
      let inj ← mk_const inj_name
      let inj_type ← infer_type inj
      let inj_arity ← get_pi_arity inj_type
      let num_equations := (inj_type.nth_binding_body (inj_arity - 1)).binding_domain.pi_arity
      let tgt ← target
      let proof ← mk_mapp inj_name (List.repeat none (inj_arity - 3) ++ [some h, some tgt])
      eapply proof
      intron_with num_equations ns base offset
    else do
      let tgt ← target
      let inductive_name := constructor_left.get_prefix
      let pr ← mk_app (inductive_name <.> "no_confusion") [tgt, lhs, rhs, h]
      exact pr
      return ([], ns)

/-- Simplify the equation `h` using injectivity of constructors. See
`injection_with`. Returns the hypotheses that were added to the context, or an
empty list if the goal was solved by contradiction.
-/
unsafe def injection (h : expr) (base := `h) (offset := some 1) : tactic (List expr) :=
  Prod.fst <$> injection_with h [] base offset

private unsafe def injections_with_inner (base : Name) (offset : Option ℕ) : ℕ → List expr → List Name → tactic Unit
  | 0, lc, ns => fail "recursion depth exceeded"
  | n + 1, [], ns => skip
  | n + 1, h :: lc, ns => do
    let o ← try_core (injection_with h ns base offset)
    match o with
      | none => injections_with_inner (n + 1) lc ns
      | some ([], _) => skip
      | some (t, ns') => injections_with_inner n (t ++ lc) ns'

/-- Simplifies equations in the context using injectivity of constructors. For
each equation `h : C x₁ ... xₙ = D y₁ ... yₘ` in the context, where `C` and `D`
are constructors of the same data type, `injections_with` does the following:

- If `C = D`, it adds equations `x₁ = y₁`, ..., `xₙ = yₙ`.
- If `C ≠ D`, it solves the goal by contradiction.

See `injection_with` for details, including information about `base` and
`offset`.

`injections_with` also recurses into the new equations `xᵢ = yᵢ`. If it has to
recurse more than five times, it fails.
-/
unsafe def injections_with (ns : List Name) (base := `h) (offset := some 1) : tactic Unit := do
  let lc ← local_context
  injections_with_inner base offset 5 lc ns

end Tactic

