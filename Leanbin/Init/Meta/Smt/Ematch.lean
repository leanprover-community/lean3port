/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.smt.ematch
! leanprover-community/mathlib commit 4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Smt.CongruenceClosure
import Leanbin.Init.Meta.Attribute
import Leanbin.Init.Meta.SimpTactic
import Leanbin.Init.Meta.InteractiveBase
import Leanbin.Init.Meta.Derive

open Tactic

/-- Heuristic instantiation lemma -/
unsafe axiom hinst_lemma : Type
#align hinst_lemma hinst_lemma

unsafe axiom hinst_lemmas : Type
#align hinst_lemmas hinst_lemmas

/-- `mk_core m e as_simp`, m is used to decide which definitions will be unfolded in patterns.
   If as_simp is tt, then this tactic will try to use the left-hand-side of the conclusion
   as a pattern. -/
unsafe axiom hinst_lemma.mk_core : Transparency → expr → Bool → tactic hinst_lemma
#align hinst_lemma.mk_core hinst_lemma.mk_core

unsafe axiom hinst_lemma.mk_from_decl_core : Transparency → Name → Bool → tactic hinst_lemma
#align hinst_lemma.mk_from_decl_core hinst_lemma.mk_from_decl_core

unsafe axiom hinst_lemma.pp : hinst_lemma → tactic format
#align hinst_lemma.pp hinst_lemma.pp

unsafe axiom hinst_lemma.id : hinst_lemma → Name
#align hinst_lemma.id hinst_lemma.id

unsafe instance : has_to_tactic_format hinst_lemma :=
  ⟨hinst_lemma.pp⟩

unsafe def hinst_lemma.mk (h : expr) : tactic hinst_lemma :=
  hinst_lemma.mk_core reducible h false
#align hinst_lemma.mk hinst_lemma.mk

unsafe def hinst_lemma.mk_from_decl (h : Name) : tactic hinst_lemma :=
  hinst_lemma.mk_from_decl_core reducible h false
#align hinst_lemma.mk_from_decl hinst_lemma.mk_from_decl

unsafe axiom hinst_lemmas.mk : hinst_lemmas
#align hinst_lemmas.mk hinst_lemmas.mk

unsafe axiom hinst_lemmas.add : hinst_lemmas → hinst_lemma → hinst_lemmas
#align hinst_lemmas.add hinst_lemmas.add

unsafe axiom hinst_lemmas.fold {α : Type} : hinst_lemmas → α → (hinst_lemma → α → α) → α
#align hinst_lemmas.fold hinst_lemmas.fold

unsafe axiom hinst_lemmas.merge : hinst_lemmas → hinst_lemmas → hinst_lemmas
#align hinst_lemmas.merge hinst_lemmas.merge

unsafe def mk_hinst_singleton : hinst_lemma → hinst_lemmas :=
  hinst_lemmas.add hinst_lemmas.mk
#align mk_hinst_singleton mk_hinst_singleton

unsafe def hinst_lemmas.pp (s : hinst_lemmas) : tactic format :=
  let tac :=
    s.fold (return format.nil) fun h tac => do
      let hpp ← h.pp
      let r ← tac
      if r then return hpp
        else
          return
            f! "{r },
              {hpp}"
  do
  let r ← tac
  return <| format.cbrace (format.group r)
#align hinst_lemmas.pp hinst_lemmas.pp

unsafe instance : has_to_tactic_format hinst_lemmas :=
  ⟨hinst_lemmas.pp⟩

open Tactic

private unsafe def add_lemma (m : Transparency) (as_simp : Bool) (h : Name) (hs : hinst_lemmas) :
    tactic hinst_lemmas := do
  let h ← hinst_lemma.mk_from_decl_core m h as_simp
  return <| hs h
#align add_lemma add_lemma

unsafe def to_hinst_lemmas_core (m : Transparency) :
    Bool → List Name → hinst_lemmas → tactic hinst_lemmas
  | as_simp, [], hs => return hs
  | as_simp, n :: ns, hs =>
    let add (n) := add_lemma m as_simp n hs >>= to_hinst_lemmas_core as_simp ns
    do
    let eqns
      ←-- First check if n is the name of a function with equational lemmas associated with it
          tactic.get_eqn_lemmas_for
          true n
    match eqns with
      | [] => do
        -- n is not the name of a function definition or it does not have equational lemmas, then check if it is a lemma
            add
            n
      | _ => do
        let p ← is_prop_decl n
        if p then add n
          else-- n is a proposition
          do
            let new_hs
              ←-- Add equational lemmas to resulting hinst_lemmas
                  to_hinst_lemmas_core
                  tt eqns hs
            to_hinst_lemmas_core as_simp ns new_hs
#align to_hinst_lemmas_core to_hinst_lemmas_core

unsafe def mk_hinst_lemma_attr_core (attr_name : Name) (as_simp : Bool) : Tactic := do
  let t := q(user_attribute hinst_lemmas)
  let v :=
    q(({  Name := attr_name
          descr := "hinst_lemma attribute"
          after_set :=
            some fun n _ _ =>
              to_hinst_lemmas_core reducible as_simp [n] hinst_lemmas.mk >> skip <|>
                fail f! "invalid ematch lemma '{n}'"
          -- allow unsetting
          before_unset := some fun _ _ => skip
          cache_cfg :=
            { mk_cache := fun ns => to_hinst_lemmas_core reducible as_simp ns hinst_lemmas.mk
              dependencies := [`reducibility] } } :
        user_attribute hinst_lemmas))
  add_decl (declaration.defn attr_name [] t v ReducibilityHints.abbrev ff)
  attribute.register attr_name
#align mk_hinst_lemma_attr_core mk_hinst_lemma_attr_core

unsafe def mk_hinst_lemma_attrs_core (as_simp : Bool) : List Name → Tactic
  | [] => skip
  | n :: ns =>
    mk_hinst_lemma_attr_core n as_simp >> mk_hinst_lemma_attrs_core ns <|> do
      let type ← infer_type (expr.const n [])
      let expected := q(user_attribute)
      is_def_eq type expected <|>
          fail
            f! "failed to create hinst_lemma attribute '{n}', declaration already exists and has different type."
      mk_hinst_lemma_attrs_core ns
#align mk_hinst_lemma_attrs_core mk_hinst_lemma_attrs_core

unsafe def merge_hinst_lemma_attrs (m : Transparency) (as_simp : Bool) :
    List Name → hinst_lemmas → tactic hinst_lemmas
  | [], hs => return hs
  | attr :: attrs, hs => do
    let ns ← attribute.get_instances attr
    let new_hs ← to_hinst_lemmas_core m as_simp ns hs
    merge_hinst_lemma_attrs attrs new_hs
#align merge_hinst_lemma_attrs merge_hinst_lemma_attrs

/-- Create a new "cached" attribute (attr_name : user_attribute hinst_lemmas).
It also creates "cached" attributes for each attr_names and simp_attr_names if they have not been defined
yet. Moreover, the hinst_lemmas for attr_name will be the union of the lemmas tagged with
    attr_name, attrs_name, and simp_attr_names.
For the ones in simp_attr_names, we use the left-hand-side of the conclusion as the pattern.
-/
unsafe def mk_hinst_lemma_attr_set (attr_name : Name) (attr_names : List Name)
    (simp_attr_names : List Name) : Tactic := do
  mk_hinst_lemma_attrs_core ff attr_names
  mk_hinst_lemma_attrs_core tt simp_attr_names
  let t := q(user_attribute hinst_lemmas)
  let v :=
    q(({  Name := attr_name
          descr := "hinst_lemma attribute set"
          after_set :=
            some fun n _ _ =>
              to_hinst_lemmas_core reducible false [n] hinst_lemmas.mk >> skip <|>
                fail f! "invalid ematch lemma '{n}'"
          -- allow unsetting
          before_unset := some fun _ _ => skip
          cache_cfg :=
            { mk_cache := fun ns => do
                let hs₁ ← to_hinst_lemmas_core reducible false ns hinst_lemmas.mk
                let hs₂ ← merge_hinst_lemma_attrs reducible false attr_names hs₁
                merge_hinst_lemma_attrs reducible tt simp_attr_names hs₂
              dependencies := [`reducibility] ++ attr_names ++ simp_attr_names } } :
        user_attribute hinst_lemmas))
  add_decl (declaration.defn attr_name [] t v ReducibilityHints.abbrev ff)
  attribute.register attr_name
#align mk_hinst_lemma_attr_set mk_hinst_lemma_attr_set

unsafe def get_hinst_lemmas_for_attr (attr_name : Name) : tactic hinst_lemmas :=
  get_attribute_cache_dyn attr_name
#align get_hinst_lemmas_for_attr get_hinst_lemmas_for_attr

structure EmatchConfig where
  maxInstances : Nat := 10000
  maxGeneration : Nat := 10
#align ematch_config EmatchConfig

/-! Ematching -/


unsafe axiom ematch_state : Type
#align ematch_state ematch_state

unsafe axiom ematch_state.mk : EmatchConfig → ematch_state
#align ematch_state.mk ematch_state.mk

unsafe axiom ematch_state.internalize : ematch_state → expr → tactic ematch_state
#align ematch_state.internalize ematch_state.internalize

namespace Tactic

unsafe axiom ematch_core :
    Transparency →
      cc_state →
        ematch_state → hinst_lemma → expr → tactic (List (expr × expr) × cc_state × ematch_state)
#align tactic.ematch_core tactic.ematch_core

unsafe axiom ematch_all_core :
    Transparency →
      cc_state →
        ematch_state → hinst_lemma → Bool → tactic (List (expr × expr) × cc_state × ematch_state)
#align tactic.ematch_all_core tactic.ematch_all_core

unsafe def ematch :
    cc_state →
      ematch_state → hinst_lemma → expr → tactic (List (expr × expr) × cc_state × ematch_state) :=
  ematch_core reducible
#align tactic.ematch tactic.ematch

unsafe def ematch_all :
    cc_state →
      ematch_state → hinst_lemma → Bool → tactic (List (expr × expr) × cc_state × ematch_state) :=
  ematch_all_core reducible
#align tactic.ematch_all tactic.ematch_all

end Tactic

