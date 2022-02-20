/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Smt.SmtTactic
import Leanbin.Init.Meta.FunInfo
import Leanbin.Init.Meta.RbMap

def Tactic.IdTag.rsimp : Unit :=
  ()

open Tactic

private unsafe def add_lemma (m : Transparency) (h : Name) (hs : hinst_lemmas) : tactic hinst_lemmas :=
  (do
      let h ← hinst_lemma.mk_from_decl_core m h true
      return <| hs h) <|>
    return hs

private unsafe def to_hinst_lemmas (m : Transparency) (ex : name_set) : List Name → hinst_lemmas → tactic hinst_lemmas
  | [], hs => return hs
  | n :: ns, hs =>
    if ex.contains n then to_hinst_lemmas ns hs
    else
      let add n := add_lemma m n hs >>= to_hinst_lemmas ns
      do
      let eqns ← tactic.get_eqn_lemmas_for true n
      match eqns with
        | [] => add n
        | _ => mcond (is_prop_decl n) (add n) (to_hinst_lemmas eqns hs >>= to_hinst_lemmas ns)

/-- Create a rsimp attribute named `attr_name`, the attribute declaration is named `attr_decl_name`.
    The cached hinst_lemmas structure is built using the lemmas marked with simp attribute `simp_attr_name`,
    but *not* marked with `ex_attr_name`.

    We say `ex_attr_name` is the "exception set". It is useful for excluding lemmas in `simp_attr_name`
    which are not good or redundant for ematching. -/
unsafe def mk_hinst_lemma_attr_from_simp_attr (attr_decl_name attr_name : Name) (simp_attr_name : Name)
    (ex_attr_name : Name) : Tactic Unit := do
  let t := quote.1 (user_attribute hinst_lemmas)
  let v :=
    quote.1
      ({ Name := attr_name, descr := s! "hinst_lemma attribute derived from '{simp_attr_name}'",
        cache_cfg :=
          { mk_cache := fun ns =>
              let aux := simp_attr_name
              let ex_attr := ex_attr_name
              do
              let hs ← to_hinst_lemmas reducible mk_name_set ns hinst_lemmas.mk
              let ss ← attribute.get_instances aux
              let ex ← get_name_set_for_attr ex_attr
              to_hinst_lemmas reducible ex ss hs,
            dependencies := [`reducibility, simp_attr_name] } } :
        user_attribute hinst_lemmas)
  add_decl (declaration.defn attr_decl_name [] t v ReducibilityHints.abbrev ff)
  attribute.register attr_decl_name

run_cmd
  mk_name_set_attr `no_rsimp

run_cmd
  mk_hinst_lemma_attr_from_simp_attr `rsimp_attr `rsimp `simp `no_rsimp

/- The following lemmas are not needed by rsimp, and they actually hurt performance since they generate a lot of
   instances. -/
attribute [no_rsimp]
  id.def Ne.def not_true not_false_iff ne_self_iff_false eq_self_iff_true heq_self_iff_true iff_not_selfₓ not_iff_selfₓ true_iff_false false_iff_true And.comm And.assoc And.left_comm and_trueₓ true_andₓ and_falseₓ false_andₓ not_and_selfₓ and_not_selfₓ and_selfₓ Or.comm Or.assoc Or.left_comm or_trueₓ true_orₓ or_falseₓ false_orₓ or_selfₓ iff_trueₓ true_iffₓ iff_falseₓ false_iffₓ iff_selfₓ implies_true_iff false_implies_iff if_t_t if_true if_false

namespace Rsimp

unsafe def is_value_like : expr → Bool
  | e =>
    if ¬e.is_app then false
    else
      let fn := e.get_app_fn
      if ¬fn.is_constant then false
      else
        let nargs := e.get_app_num_args
        let fname := fn.const_name
        if fname = `` Zero.zero ∧ nargs = 2 then true
        else
          if fname = `` One.one ∧ nargs = 2 then true
          else
            if fname = `` bit0 ∧ nargs = 3 then is_value_like e.app_arg
            else
              if fname = `` bit1 ∧ nargs = 4 then is_value_like e.app_arg
              else if fname = `` Charₓ.ofNat ∧ nargs = 1 then is_value_like e.app_arg else false

/-- Return the size of term by considering only explicit arguments. -/
unsafe def explicit_size : expr → tactic Nat
  | e =>
    if ¬e.is_app then return 1
    else
      if is_value_like e then return 1
      else
        fold_explicit_args e 1 fun n arg => do
          let r ← explicit_size arg
          return <| r + n

/-- Choose smallest element (with respect to explicit_size) in `e`s equivalence class. -/
unsafe def choose (ccs : cc_state) (e : expr) : tactic expr := do
  let sz ← explicit_size e
  let p ←
    (ccs.mfold_eqc e (e, sz)) fun p e' =>
        if p.2 = 1 then return p
        else do
          let sz' ← explicit_size e'
          if sz' < p.2 then return (e', sz') else return p
  return p.1

unsafe def repr_map :=
  expr_map expr

unsafe def mk_repr_map :=
  expr_map.mk expr

unsafe def to_repr_map (ccs : cc_state) : tactic repr_map :=
  ccs.roots.mfoldl
    (fun S e => do
      let r ← choose ccs e
      return <| S e r)
    mk_repr_map

unsafe def rsimplify (ccs : cc_state) (e : expr) (m : Option repr_map := none) : tactic (expr × expr) := do
  let m ←
    match m with
      | none => to_repr_map ccs
      | some m => return m
  let r ←
    simplify_top_down ()
        (fun _ t => do
          let root ← return <| ccs.root t
          let new_t ← m.find root
          guardₓ ¬expr.alpha_eqv new_t t
          let prf ← ccs.eqv_proof t new_t
          return ((), new_t, prf))
        e
  return r.2

structure Config where
  attrName := `rsimp_attr
  maxRounds := 8

open SmtTactic

private def tagged_proof.rsimp : Unit :=
  ()

unsafe def collect_implied_eqs (cfg : Config := {  }) (extra := hinst_lemmas.mk) : tactic cc_state := do
  focus1 <|
      using_smt_with { emAttr := cfg } <| do
        add_lemmas_from_facts
        add_lemmas extra
        iterate_at_most cfg (ematch >> try smt_tactic.close)
        done >> return cc_state.mk <|> to_cc_state

unsafe def rsimplify_goal (ccs : cc_state) (m : Option repr_map := none) : tactic Unit := do
  let t ← target
  let (new_t, pr) ← rsimplify ccs t m
  try (replace_target new_t pr `` id_tag.rsimp)

unsafe def rsimplify_at (ccs : cc_state) (h : expr) (m : Option repr_map := none) : tactic Unit := do
  when (expr.is_local_constant h = ff)
      (tactic.fail "tactic rsimplify_at failed, the given expression is not a hypothesis")
  let htype ← infer_type h
  let (new_htype, HEq) ← rsimplify ccs htype m
  try <| do
      assert (expr.local_pp_name h) new_htype
      mk_eq_mp HEq h >>= exact
      try <| clear h

end Rsimp

open Rsimp

namespace Tactic

unsafe def rsimp (cfg : Config := {  }) (extra := hinst_lemmas.mk) : tactic Unit := do
  let ccs ← collect_implied_eqs cfg extra
  try <| rsimplify_goal ccs

unsafe def rsimp_at (h : expr) (cfg : Config := {  }) (extra := hinst_lemmas.mk) : tactic Unit := do
  let ccs ← collect_implied_eqs cfg extra
  try <| rsimplify_at ccs h

namespace Interactive

-- TODO(Leo): allow user to provide extra lemmas manually
unsafe def rsimp : tactic Unit :=
  tactic.rsimp

end Interactive

end Tactic

