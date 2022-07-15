/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Attribute that can automatically derive typeclass instances.
-/
prelude
import Leanbin.Init.Meta.Attribute
import Leanbin.Init.Meta.InteractiveBase
import Leanbin.Init.Meta.MkHasReflectInstance
import Leanbin.Init.Meta.MkHasSizeofInstance
import Leanbin.Init.Meta.MkInhabitedInstance

open Lean

open Interactive.Types

open Tactic

/-- A handler that may or may not be able to implement the typeclass `cls` for `decl`.
    It should return `tt` if it was able to derive `cls` and `ff` if it does not know
    how to derive `cls`, in which case lower-priority handlers will be tried next. -/
unsafe def derive_handler :=
  ∀ cls : pexpr decl : Name, tactic Bool

@[user_attribute]
unsafe def derive_handler_attr : user_attribute where
  Name := `derive_handler
  descr := "register a definition of type `derive_handler` for use in the [derive] attribute"

private unsafe def try_handlers (p : pexpr) (n : Name) : List derive_handler → tactic Unit
  | [] => fail f! "failed to find a derive handler for '{p}'"
  | h :: hs => do
    let success ← h p n
    when ¬success <| try_handlers hs

@[user_attribute]
unsafe def derive_attr : user_attribute Unit (List pexpr) where
  Name := `derive
  descr := "automatically derive typeclass instances"
  parser := pexpr_list_or_texpr
  after_set :=
    some fun n _ _ => do
      let ps ← derive_attr.get_param n
      let handlers ← attribute.get_instances `derive_handler
      let handlers ← handlers.mmap fun n => eval_expr derive_handler (expr.const n [])
      ps fun p => try_handlers p n handlers

/-- Given a tactic `tac` that can solve an application of `cls` in the right context,
    `instance_derive_handler` uses it to build an instance declaration of `cls n`. -/
unsafe def instance_derive_handler (cls : Name) (tac : tactic Unit) (univ_poly := true)
    (modify_target : Name → List expr → expr → tactic expr := fun _ _ => pure) : derive_handler := fun p n =>
  if p.is_constant_of cls then do
    let decl ← get_decl n
    let cls_decl ← get_decl cls
    let env ← get_env
    guardₓ (env n) <|> fail f! "failed to derive '{cls }', '{n}' is not an inductive type"
    let ls := decl.univ_params.map fun n => if univ_poly then level.param n else level.zero
    let-- incrementally build up target expression `Π (hp : p) [cls hp] ..., cls (n.{ls} hp ...)`
    -- where `p ...` are the inductive parameter types of `n`
    tgt : expr := expr.const n ls
    let ⟨params, _⟩ ← mk_local_pis (decl.type.instantiate_univ_params (decl.univ_params.zip ls))
    let tgt := tgt.mk_app params
    let tgt ← mk_app cls [tgt]
    let tgt ← modify_target n params tgt
    let tgt ←
      params.enum.mfoldr
          (fun ⟨i, param⟩ tgt => do
            let tgt ←
              (-- add typeclass hypothesis for each inductive parameter
                  -- TODO(sullrich): omit some typeclass parameters based on usage of `param`?
                  do
                    guardₓ <| i < env n
                    let param_cls ← mk_app cls [param]
                    pure <| expr.pi `a BinderInfo.inst_implicit param_cls tgt) <|>
                  pure tgt
            pure <| tgt param)
          tgt
    let (_, val) ← tactic.solve_aux tgt (intros >> tac)
    let val ← instantiate_mvars val
    let trusted := decl.is_trusted ∧ cls_decl.is_trusted
    add_protected_decl
        (declaration.defn (n ++ cls) (if univ_poly then decl else []) tgt val ReducibilityHints.abbrev trusted)
    set_basic_attribute `instance (n ++ cls) tt
    pure True
  else pure False

@[derive_handler]
unsafe def has_reflect_derive_handler :=
  instance_derive_handler `` has_reflect mk_has_reflect_instance false fun n params tgt =>
    -- add additional `reflected` assumption for each parameter
        params.mfoldr
      (fun param tgt => do
        let param_cls ← mk_mapp `reflected [none, some param]
        pure <| expr.pi `a BinderInfo.inst_implicit param_cls tgt)
      tgt

@[derive_handler]
unsafe def has_sizeof_derive_handler :=
  instance_derive_handler `` SizeOf mk_has_sizeof_instance

deriving instance has_reflect for Bool, Prod, Sum, Option, Interactive.Loc, Pos

