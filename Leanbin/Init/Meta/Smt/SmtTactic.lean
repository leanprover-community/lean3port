/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.smt.smt_tactic
! leanprover-community/lean commit 4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Control.Default
import Leanbin.Init.Meta.SimpTactic
import Leanbin.Init.Meta.Smt.CongruenceClosure
import Leanbin.Init.Meta.Smt.Ematch

universe u

run_cmd
  mk_simp_attr `pre_smt

run_cmd
  mk_hinst_lemma_attr_set `ematch [] [`ematch_lhs]

/-- Configuration for the smt tactic preprocessor. The preprocessor
  is applied whenever a new hypothesis is introduced.

  - simp_attr: is the attribute name for the simplification lemmas
    that are used during the preprocessing step.

  - max_steps: it is the maximum number of steps performed by the simplifier.

  - zeta: if tt, then zeta reduction (i.e., unfolding let-expressions)
    is used during preprocessing.
-/
structure SmtPreConfig where
  simpAttr : Name := `pre_smt
  maxSteps : Nat := 1000000
  zeta : Bool := false
#align smt_pre_config SmtPreConfig

/-- Configuration for the smt_state object.

- em_attr: is the attribute name for the hinst_lemmas
  that are used for ematching -/
structure SmtConfig where
  ccCfg : CcConfig := { }
  emCfg : EmatchConfig := { }
  preCfg : SmtPreConfig := { }
  emAttr : Name := `ematch
#align smt_config SmtConfig

unsafe def smt_config.set_classical (c : SmtConfig) (b : Bool) : SmtConfig :=
  { c with ccCfg := { c.ccCfg with em := b } }
#align smt_config.set_classical smt_config.set_classical

unsafe axiom smt_goal : Type
#align smt_goal smt_goal

unsafe def smt_state :=
  List smt_goal
#align smt_state smt_state

unsafe axiom smt_state.mk : SmtConfig → tactic smt_state
#align smt_state.mk smt_state.mk

unsafe axiom smt_state.to_format : smt_state → tactic_state → format
#align smt_state.to_format smt_state.to_format

/-- Return tt iff classical excluded middle was enabled at  smt_state.mk -/
unsafe axiom smt_state.classical : smt_state → Bool
#align smt_state.classical smt_state.classical

unsafe def smt_tactic :=
  StateT smt_state tactic
#align smt_tactic smt_tactic

unsafe instance : Append smt_state :=
  List.hasAppend

section

attribute [local reducible] smt_tactic

unsafe instance : Monad smt_tactic := by infer_instance

unsafe instance : Alternative smt_tactic := by infer_instance

unsafe instance : MonadState smt_state smt_tactic := by infer_instance

end

/- We don't use the default state_t lift operation because only
   tactics that do not change hypotheses can be automatically lifted to smt_tactic. -/
unsafe axiom tactic_to_smt_tactic (α : Type) : tactic α → smt_tactic α
#align tactic_to_smt_tactic tactic_to_smt_tactic

unsafe instance : HasMonadLift tactic smt_tactic :=
  ⟨tactic_to_smt_tactic⟩

unsafe instance (α : Type) : Coe (tactic α) (smt_tactic α) :=
  ⟨monadLift⟩

unsafe instance : MonadFail smt_tactic :=
  { smt_tactic.monad with fail := fun α s => (tactic.fail (to_fmt s) : smt_tactic α) }

namespace SmtTactic

open Tactic (Transparency)

unsafe axiom intros : smt_tactic Unit
#align smt_tactic.intros smt_tactic.intros

unsafe axiom intron : Nat → smt_tactic Unit
#align smt_tactic.intron smt_tactic.intron

unsafe axiom intro_lst : List Name → smt_tactic Unit
#align smt_tactic.intro_lst smt_tactic.intro_lst

/-- Try to close main goal by using equalities implied by the congruence
  closure module.
-/
unsafe axiom close : smt_tactic Unit
#align smt_tactic.close smt_tactic.close

/-- Produce new facts using heuristic lemma instantiation based on E-matching.
  This tactic tries to match patterns from lemmas in the main goal with terms
  in the main goal. The set of lemmas is populated with theorems
  tagged with the attribute specified at smt_config.em_attr, and lemmas
  added using tactics such as `smt_tactic.add_lemmas`.
  The current set of lemmas can be retrieved using the tactic `smt_tactic.get_lemmas`.

  Remark: the given predicate is applied to every new instance. The instance
  is only added to the state if the predicate returns tt.
-/
unsafe axiom ematch_core : (expr → Bool) → smt_tactic Unit
#align smt_tactic.ematch_core smt_tactic.ematch_core

/-- Produce new facts using heuristic lemma instantiation based on E-matching.
  This tactic tries to match patterns from the given lemmas with terms in
  the main goal.
-/
unsafe axiom ematch_using : hinst_lemmas → smt_tactic Unit
#align smt_tactic.ematch_using smt_tactic.ematch_using

unsafe axiom mk_ematch_eqn_lemmas_for_core : Transparency → Name → smt_tactic hinst_lemmas
#align smt_tactic.mk_ematch_eqn_lemmas_for_core smt_tactic.mk_ematch_eqn_lemmas_for_core

unsafe axiom to_cc_state : smt_tactic cc_state
#align smt_tactic.to_cc_state smt_tactic.to_cc_state

unsafe axiom to_em_state : smt_tactic ematch_state
#align smt_tactic.to_em_state smt_tactic.to_em_state

unsafe axiom get_config : smt_tactic SmtConfig
#align smt_tactic.get_config smt_tactic.get_config

/-- Preprocess the given term using the same simplifications rules used when
  we introduce a new hypothesis. The result is pair containing the resulting
  term and a proof that it is equal to the given one.
-/
unsafe axiom preprocess : expr → smt_tactic (expr × expr)
#align smt_tactic.preprocess smt_tactic.preprocess

unsafe axiom get_lemmas : smt_tactic hinst_lemmas
#align smt_tactic.get_lemmas smt_tactic.get_lemmas

unsafe axiom set_lemmas : hinst_lemmas → smt_tactic Unit
#align smt_tactic.set_lemmas smt_tactic.set_lemmas

unsafe axiom add_lemmas : hinst_lemmas → smt_tactic Unit
#align smt_tactic.add_lemmas smt_tactic.add_lemmas

unsafe def add_ematch_lemma_core (md : Transparency) (as_simp : Bool) (e : expr) :
    smt_tactic Unit := do
  let h ← hinst_lemma.mk_core md e as_simp
  add_lemmas (mk_hinst_singleton h)
#align smt_tactic.add_ematch_lemma_core smt_tactic.add_ematch_lemma_core

unsafe def add_ematch_lemma_from_decl_core (md : Transparency) (as_simp : Bool) (n : Name) :
    smt_tactic Unit := do
  let h ← hinst_lemma.mk_from_decl_core md n as_simp
  add_lemmas (mk_hinst_singleton h)
#align smt_tactic.add_ematch_lemma_from_decl_core smt_tactic.add_ematch_lemma_from_decl_core

unsafe def add_ematch_eqn_lemmas_for_core (md : Transparency) (n : Name) : smt_tactic Unit := do
  let hs ← mk_ematch_eqn_lemmas_for_core md n
  add_lemmas hs
#align smt_tactic.add_ematch_eqn_lemmas_for_core smt_tactic.add_ematch_eqn_lemmas_for_core

unsafe def ematch : smt_tactic Unit :=
  ematch_core fun _ => true
#align smt_tactic.ematch smt_tactic.ematch

unsafe def failed {α} : smt_tactic α :=
  tactic.failed
#align smt_tactic.failed smt_tactic.failed

unsafe def fail {α : Type} {β : Type u} [has_to_format β] (msg : β) : smt_tactic α :=
  tactic.fail msg
#align smt_tactic.fail smt_tactic.fail

unsafe def try {α : Type} (t : smt_tactic α) : smt_tactic Unit :=
  ⟨fun ss ts =>
    result.cases_on (t.run ss ts) (fun ⟨a, new_ss⟩ => result.success ((), new_ss)) fun e ref s' =>
      result.success ((), ss) ts⟩
#align smt_tactic.try smt_tactic.try

/-- `iterate_at_most n t`: repeat the given tactic at most n times or until t fails -/
unsafe def iterate_at_most : Nat → smt_tactic Unit → smt_tactic Unit
  | 0, t => return ()
  | n + 1, t =>
    (do
        t
        iterate_at_most n t) <|>
      return ()
#align smt_tactic.iterate_at_most smt_tactic.iterate_at_most

/-- `iterate_exactly n t` : execute t n times -/
unsafe def iterate_exactly : Nat → smt_tactic Unit → smt_tactic Unit
  | 0, t => return ()
  | n + 1, t => do
    t
    iterate_exactly n t
#align smt_tactic.iterate_exactly smt_tactic.iterate_exactly

unsafe def iterate : smt_tactic Unit → smt_tactic Unit :=
  iterate_at_most 100000
#align smt_tactic.iterate smt_tactic.iterate

unsafe def eblast : smt_tactic Unit :=
  iterate (ematch >> try close)
#align smt_tactic.eblast smt_tactic.eblast

open Tactic

protected unsafe def read : smt_tactic (smt_state × tactic_state) := do
  let s₁ ← get
  let s₂ ← tactic.read
  return (s₁, s₂)
#align smt_tactic.read smt_tactic.read

protected unsafe def write : smt_state × tactic_state → smt_tactic Unit := fun ⟨ss, ts⟩ =>
  ⟨fun _ _ => result.success ((), ss) ts⟩
#align smt_tactic.write smt_tactic.write

private unsafe def mk_smt_goals_for (cfg : SmtConfig) :
    List expr → List smt_goal → List expr → tactic (List smt_goal × List expr)
  | [], sr, tr => return (sr.reverse, tr.reverse)
  | tg :: tgs, sr, tr => do
    tactic.set_goals [tg]
    let [new_sg] ← smt_state.mk cfg |
      tactic.failed
    let [new_tg] ← get_goals |
      tactic.failed
    mk_smt_goals_for tgs (new_sg :: sr) (new_tg :: tr)
#align smt_tactic.mk_smt_goals_for smt_tactic.mk_smt_goals_for

/-- See slift -/
unsafe def slift_aux {α : Type} (t : tactic α) (cfg : SmtConfig) : smt_tactic α :=
  ⟨fun ss => do
    let _ :: sgs ← return ss |
      tactic.fail "slift tactic failed, there no smt goals to be solved"
    let tg :: tgs ← tactic.get_goals |
      tactic.failed
    tactic.set_goals [tg]
    let a ← t
    let new_tgs ← tactic.get_goals
    let (new_sgs, new_tgs) ← mk_smt_goals_for cfg new_tgs [] []
    tactic.set_goals (new_tgs ++ tgs)
    return (a, new_sgs ++ sgs)⟩
#align smt_tactic.slift_aux smt_tactic.slift_aux

/-- This lift operation will restart the SMT state.
  It is useful for using tactics that change the set of hypotheses. -/
unsafe def slift {α : Type} (t : tactic α) : smt_tactic α :=
  get_config >>= slift_aux t
#align smt_tactic.slift smt_tactic.slift

unsafe def trace_state : smt_tactic Unit := do
  let (s₁, s₂) ← smt_tactic.read
  trace (smt_state.to_format s₁ s₂)
#align smt_tactic.trace_state smt_tactic.trace_state

unsafe def trace {α : Type} [has_to_tactic_format α] (a : α) : smt_tactic Unit :=
  tactic.trace a
#align smt_tactic.trace smt_tactic.trace

unsafe def to_expr (q : pexpr) (allow_mvars := true) : smt_tactic expr :=
  tactic.to_expr q allow_mvars
#align smt_tactic.to_expr smt_tactic.to_expr

unsafe def classical : smt_tactic Bool := do
  let s ← get
  return s
#align smt_tactic.classical smt_tactic.classical

unsafe def num_goals : smt_tactic Nat :=
  List.length <$> get
#align smt_tactic.num_goals smt_tactic.num_goals

-- Low level primitives for managing set of goals
unsafe def get_goals : smt_tactic (List smt_goal × List expr) := do
  let (g₁, _) ← smt_tactic.read
  let g₂ ← tactic.get_goals
  return (g₁, g₂)
#align smt_tactic.get_goals smt_tactic.get_goals

unsafe def set_goals : List smt_goal → List expr → smt_tactic Unit := fun g₁ g₂ =>
  ⟨fun ss => tactic.set_goals g₂ >> return ((), g₁)⟩
#align smt_tactic.set_goals smt_tactic.set_goals

private unsafe def all_goals_core (tac : smt_tactic Unit) :
    List smt_goal → List expr → List smt_goal → List expr → smt_tactic Unit
  | [], ts, acs, act => set_goals acs (ts ++ act)
  | s :: ss, [], acs, act => fail "ill-formed smt_state"
  | s :: ss, t :: ts, acs, act => do
    set_goals [s] [t]
    tac
    let (new_ss, new_ts) ← get_goals
    all_goals_core ss ts (acs ++ new_ss) (act ++ new_ts)
#align smt_tactic.all_goals_core smt_tactic.all_goals_core

/-- Apply the given tactic to all goals. -/
unsafe def all_goals (tac : smt_tactic Unit) : smt_tactic Unit := do
  let (ss, ts) ← get_goals
  all_goals_core tac ss ts [] []
#align smt_tactic.all_goals smt_tactic.all_goals

/--
LCF-style AND_THEN tactic. It applies tac1, and if succeed applies tac2 to each subgoal produced by tac1 -/
unsafe def seq (tac1 : smt_tactic Unit) (tac2 : smt_tactic Unit) : smt_tactic Unit := do
  let (s :: ss, t :: ts) ← get_goals
  set_goals [s] [t]
  tac1
  all_goals tac2
  let (new_ss, new_ts) ← get_goals
  set_goals (new_ss ++ ss) (new_ts ++ ts)
#align smt_tactic.seq smt_tactic.seq

unsafe instance : AndThen' (smt_tactic Unit) (smt_tactic Unit) (smt_tactic Unit) :=
  ⟨seq⟩

unsafe def focus1 {α} (tac : smt_tactic α) : smt_tactic α := do
  let (s :: ss, t :: ts) ← get_goals
  match ss with
    | [] => tac
    | _ => do
      set_goals [s] [t]
      let a ← tac
      let (ss', ts') ← get_goals
      set_goals (ss' ++ ss) (ts' ++ ts)
      return a
#align smt_tactic.focus1 smt_tactic.focus1

unsafe def solve1 (tac : smt_tactic Unit) : smt_tactic Unit := do
  let (ss, gs) ← get_goals
  match ss, gs with
    | [], _ => fail "solve1 tactic failed, there isn't any goal left to focus"
    | _, [] => fail "solve1 tactic failed, there isn't any smt goal left to focus"
    | s :: ss, g :: gs => do
      set_goals [s] [g]
      tac
      let (ss', gs') ← get_goals
      match ss', gs' with
        | [], [] => set_goals ss gs
        | _, _ => fail "solve1 tactic failed, focused goal has not been solved"
#align smt_tactic.solve1 smt_tactic.solve1

unsafe def swap : smt_tactic Unit := do
  let (ss, ts) ← get_goals
  match ss, ts with
    | s₁ :: s₂ :: ss, t₁ :: t₂ :: ts => set_goals (s₂ :: s₁ :: ss) (t₂ :: t₁ :: ts)
    | _, _ => failed
#align smt_tactic.swap smt_tactic.swap

/-- Add a new goal for t, and the hypothesis (h : t) in the current goal. -/
unsafe def assert (h : Name) (t : expr) : smt_tactic Unit :=
  (((tactic.assert_core h t >> swap) >> intros) >> swap) >> try close
#align smt_tactic.assert smt_tactic.assert

/-- Add the hypothesis (h : t) in the current goal if v has type t. -/
unsafe def assertv (h : Name) (t : expr) (v : expr) : smt_tactic Unit :=
  (tactic.assertv_core h t v >> intros) >> return ()
#align smt_tactic.assertv smt_tactic.assertv

/-- Add a new goal for t, and the hypothesis (h : t := ?M) in the current goal. -/
unsafe def define (h : Name) (t : expr) : smt_tactic Unit :=
  (((tactic.define_core h t >> swap) >> intros) >> swap) >> try close
#align smt_tactic.define smt_tactic.define

/-- Add the hypothesis (h : t := v) in the current goal if v has type t. -/
unsafe def definev (h : Name) (t : expr) (v : expr) : smt_tactic Unit :=
  (tactic.definev_core h t v >> intros) >> return ()
#align smt_tactic.definev smt_tactic.definev

/-- Add (h : t := pr) to the current goal -/
unsafe def pose (h : Name) (t : Option expr := none) (pr : expr) : smt_tactic Unit :=
  match t with
  | none => do
    let t ← infer_type pr
    definev h t pr
  | some t => definev h t pr
#align smt_tactic.pose smt_tactic.pose

/-- Add (h : t) to the current goal, given a proof (pr : t) -/
unsafe def note (h : Name) (t : Option expr := none) (pr : expr) : smt_tactic Unit :=
  match t with
  | none => do
    let t ← infer_type pr
    assertv h t pr
  | some t => assertv h t pr
#align smt_tactic.note smt_tactic.note

unsafe def destruct (e : expr) : smt_tactic Unit :=
  smt_tactic.seq (tactic.destruct e) smt_tactic.intros
#align smt_tactic.destruct smt_tactic.destruct

unsafe def by_cases (e : expr) : smt_tactic Unit := do
  let c ← classical
  if c then destruct (expr.app (expr.const `classical.em []) e)
    else do
      let dec_e ←
        mk_app `decidable [e] <|> fail "by_cases smt_tactic failed, type is not a proposition"
      let inst ←
        mk_instance dec_e <|>
            fail "by_cases smt_tactic failed, type of given expression is not decidable"
      let em ← mk_app `decidable.em [e, inst]
      destruct em
#align smt_tactic.by_cases smt_tactic.by_cases

unsafe def by_contradiction : smt_tactic Unit := do
  let t ← target
  let c ← classical
  if t then skip
    else
      if c then do
        apply (expr.app (expr.const `classical.by_contradiction []) t)
        intros
      else do
        let dec_t ←
          mk_app `decidable [t] <|>
              fail "by_contradiction smt_tactic failed, target is not a proposition"
        let inst ←
          mk_instance dec_t <|> fail "by_contradiction smt_tactic failed, target is not decidable"
        let a ← mk_mapp `decidable.by_contradiction [some t, some inst]
        apply a
        intros
#align smt_tactic.by_contradiction smt_tactic.by_contradiction

/-- Return a proof for e, if 'e' is a known fact in the main goal. -/
unsafe def proof_for (e : expr) : smt_tactic expr := do
  let cc ← to_cc_state
  cc e
#align smt_tactic.proof_for smt_tactic.proof_for

/--
Return a refutation for e (i.e., a proof for (not e)), if 'e' has been refuted in the main goal. -/
unsafe def refutation_for (e : expr) : smt_tactic expr := do
  let cc ← to_cc_state
  cc e
#align smt_tactic.refutation_for smt_tactic.refutation_for

unsafe def get_facts : smt_tactic (List expr) := do
  let cc ← to_cc_state
  return <| cc expr.mk_true
#align smt_tactic.get_facts smt_tactic.get_facts

unsafe def get_refuted_facts : smt_tactic (List expr) := do
  let cc ← to_cc_state
  return <| cc expr.mk_false
#align smt_tactic.get_refuted_facts smt_tactic.get_refuted_facts

unsafe def add_ematch_lemma : expr → smt_tactic Unit :=
  add_ematch_lemma_core reducible false
#align smt_tactic.add_ematch_lemma smt_tactic.add_ematch_lemma

unsafe def add_ematch_lhs_lemma : expr → smt_tactic Unit :=
  add_ematch_lemma_core reducible true
#align smt_tactic.add_ematch_lhs_lemma smt_tactic.add_ematch_lhs_lemma

unsafe def add_ematch_lemma_from_decl : Name → smt_tactic Unit :=
  add_ematch_lemma_from_decl_core reducible false
#align smt_tactic.add_ematch_lemma_from_decl smt_tactic.add_ematch_lemma_from_decl

unsafe def add_ematch_lhs_lemma_from_decl : Name → smt_tactic Unit :=
  add_ematch_lemma_from_decl_core reducible false
#align smt_tactic.add_ematch_lhs_lemma_from_decl smt_tactic.add_ematch_lhs_lemma_from_decl

unsafe def add_ematch_eqn_lemmas_for : Name → smt_tactic Unit :=
  add_ematch_eqn_lemmas_for_core reducible
#align smt_tactic.add_ematch_eqn_lemmas_for smt_tactic.add_ematch_eqn_lemmas_for

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `f -/
unsafe def add_lemmas_from_facts_core : List expr → smt_tactic Unit
  | [] => return ()
  | f :: fs => do
    try
        ((is_prop f >> guard (f && not (f f.is_arrow))) >> proof_for f >>=
          add_ematch_lemma_core reducible ff)
    add_lemmas_from_facts_core fs
#align smt_tactic.add_lemmas_from_facts_core smt_tactic.add_lemmas_from_facts_core

unsafe def add_lemmas_from_facts : smt_tactic Unit :=
  get_facts >>= add_lemmas_from_facts_core
#align smt_tactic.add_lemmas_from_facts smt_tactic.add_lemmas_from_facts

unsafe def induction (e : expr) (ids : List Name := []) (rec : Option Name := none) :
    smt_tactic Unit :=
  slift (tactic.induction e ids rec >> return ())
#align smt_tactic.induction smt_tactic.induction

-- pass on the information?
unsafe def when (c : Prop) [Decidable c] (tac : smt_tactic Unit) : smt_tactic Unit :=
  if c then tac else skip
#align smt_tactic.when smt_tactic.when

unsafe def when_tracing (n : Name) (tac : smt_tactic Unit) : smt_tactic Unit :=
  when (is_trace_enabled_for n = true) tac
#align smt_tactic.when_tracing smt_tactic.when_tracing

end SmtTactic

open SmtTactic

unsafe def using_smt {α} (t : smt_tactic α) (cfg : SmtConfig := { }) : tactic α := do
  let ss ← smt_state.mk cfg
  let (a, _) ←
    (do
            let a ← t
            iterate close
            return a).run
        ss
  return a
#align using_smt using_smt

unsafe def using_smt_with {α} (cfg : SmtConfig) (t : smt_tactic α) : tactic α :=
  using_smt t cfg
#align using_smt_with using_smt_with

