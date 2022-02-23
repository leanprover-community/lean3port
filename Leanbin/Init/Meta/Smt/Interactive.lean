/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Smt.SmtTactic
import Leanbin.Init.Meta.InteractiveBase
import Leanbin.Init.Meta.Smt.Rsimp

namespace SmtTactic

unsafe def save_info (p : Pos) : smt_tactic Unit := do
  let (ss, ts) ← smt_tactic.read
  tactic.save_info_thunk p fun _ => smt_state.to_format ss ts

unsafe def skip : smt_tactic Unit :=
  return ()

unsafe def solve_goals : smt_tactic Unit :=
  iterate close

unsafe def step {α : Type} (tac : smt_tactic α) : smt_tactic Unit :=
  tac >> solve_goals

unsafe def istep {α : Type} (line0 col0 line col ast : Nat) (tac : smt_tactic α) : smt_tactic Unit :=
  ⟨fun ss ts =>
    (@scopeTrace _ line col fun _ => tactic.with_ast ast ((tac >> solve_goals).run ss) ts).clamp_pos line0 line col⟩

unsafe def execute (tac : smt_tactic Unit) : tactic Unit :=
  using_smt tac

unsafe def execute_with (cfg : SmtConfig) (tac : smt_tactic Unit) : tactic Unit :=
  using_smt tac cfg

unsafe instance : interactive.executor smt_tactic where
  config_type := SmtConfig
  Inhabited := ⟨{  }⟩
  execute_with := fun cfg tac => using_smt tac cfg

namespace Interactive

open Lean.Parser

open _Root_.Interactive

open Interactive.Types

-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

-- mathport name: «expr *»
local postfix:1024 "*" => many

unsafe def itactic : Type :=
  smt_tactic Unit

unsafe def intros : parse ident* → smt_tactic Unit
  | [] => smt_tactic.intros
  | hs => smt_tactic.intro_lst hs

/-- Try to close main goal by using equalities implied by the congruence
  closure module.
-/
unsafe def close : smt_tactic Unit :=
  smt_tactic.close

/-- Produce new facts using heuristic lemma instantiation based on E-matching.
  This tactic tries to match patterns from lemmas in the main goal with terms
  in the main goal. The set of lemmas is populated with theorems
  tagged with the attribute specified at smt_config.em_attr, and lemmas
  added using tactics such as `smt_tactic.add_lemmas`.
  The current set of lemmas can be retrieved using the tactic `smt_tactic.get_lemmas`.
-/
unsafe def ematch : smt_tactic Unit :=
  smt_tactic.ematch

unsafe def apply (q : parse texpr) : smt_tactic Unit :=
  tactic.interactive.apply q

unsafe def fapply (q : parse texpr) : smt_tactic Unit :=
  tactic.interactive.fapply q

unsafe def apply_instance : smt_tactic Unit :=
  tactic.apply_instance

unsafe def change (q : parse texpr) : smt_tactic Unit :=
  tactic.interactive.change q none (Loc.ns [none])

unsafe def exact (q : parse texpr) : smt_tactic Unit :=
  tactic.interactive.exact q

unsafe def from :=
  exact

unsafe def assume :=
  tactic.interactive.assume

unsafe def have (h : parse ident ?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse <| (tk ":=" *> texpr)?) :
    smt_tactic Unit :=
  let h := h.getOrElse `this
  (match q₁, q₂ with
    | some e, some p => do
      let t ← tactic.to_expr e
      let v ← tactic.to_expr (pquote.1 (%%ₓp : %%ₓt))
      smt_tactic.assertv h t v
    | none, some p => do
      let p ← tactic.to_expr p
      smt_tactic.note h none p
    | some e, none => tactic.to_expr e >>= smt_tactic.assert h
    | none, none => do
      let u ← tactic.mk_meta_univ
      let e ← tactic.mk_meta_var (expr.sort u)
      smt_tactic.assert h e) >>
    return ()

unsafe def let (h : parse ident ?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse <| (tk ":=" *> texpr)?) :
    smt_tactic Unit :=
  let h := h.getOrElse `this
  (match q₁, q₂ with
    | some e, some p => do
      let t ← tactic.to_expr e
      let v ← tactic.to_expr (pquote.1 (%%ₓp : %%ₓt))
      smt_tactic.definev h t v
    | none, some p => do
      let p ← tactic.to_expr p
      smt_tactic.pose h none p
    | some e, none => tactic.to_expr e >>= smt_tactic.define h
    | none, none => do
      let u ← tactic.mk_meta_univ
      let e ← tactic.mk_meta_var (expr.sort u)
      smt_tactic.define h e) >>
    return ()

unsafe def add_fact (q : parse texpr) : smt_tactic Unit := do
  let h ← tactic.get_unused_name `h none
  let p ← tactic.to_expr_strict q
  smt_tactic.note h none p

unsafe def trace_state : smt_tactic Unit :=
  smt_tactic.trace_state

unsafe def trace {α : Type} [has_to_tactic_format α] (a : α) : smt_tactic Unit :=
  tactic.trace a

unsafe def destruct (q : parse texpr) : smt_tactic Unit := do
  let p ← tactic.to_expr_strict q
  smt_tactic.destruct p

unsafe def by_cases (q : parse texpr) : smt_tactic Unit := do
  let p ← tactic.to_expr_strict q
  smt_tactic.by_cases p

unsafe def by_contradiction : smt_tactic Unit :=
  smt_tactic.by_contradiction

unsafe def by_contra : smt_tactic Unit :=
  smt_tactic.by_contradiction

open Tactic (resolve_name Transparency to_expr)

private unsafe def report_invalid_em_lemma {α : Type} (n : Name) : smt_tactic α :=
  fail f! "invalid ematch lemma '{n}'"

private unsafe def add_lemma_name (md : Transparency) (lhs_lemma : Bool) (n : Name) (ref : pexpr) : smt_tactic Unit :=
  do
  let p ← resolve_name n
  match p with
    | expr.const n _ =>
      add_ematch_lemma_from_decl_core md lhs_lemma n >> tactic.save_const_type_info n ref <|> report_invalid_em_lemma n
    | _ =>
      (do
          let e ← to_expr p
          add_ematch_lemma_core md lhs_lemma e >> try (tactic.save_type_info e ref)) <|>
        report_invalid_em_lemma n

private unsafe def add_lemma_pexpr (md : Transparency) (lhs_lemma : Bool) (p : pexpr) : smt_tactic Unit :=
  match p with
  | expr.const c [] => add_lemma_name md lhs_lemma c p
  | expr.local_const c _ _ _ => add_lemma_name md lhs_lemma c p
  | _ => do
    let new_e ← to_expr p
    add_ematch_lemma_core md lhs_lemma new_e

private unsafe def add_lemma_pexprs (md : Transparency) (lhs_lemma : Bool) : List pexpr → smt_tactic Unit
  | [] => return ()
  | p :: ps => add_lemma_pexpr md lhs_lemma p >> add_lemma_pexprs ps

unsafe def add_lemma (l : parse pexpr_list_or_texpr) : smt_tactic Unit :=
  add_lemma_pexprs reducible false l

unsafe def add_lhs_lemma (l : parse pexpr_list_or_texpr) : smt_tactic Unit :=
  add_lemma_pexprs reducible true l

private unsafe def add_eqn_lemmas_for_core (md : Transparency) : List Name → smt_tactic Unit
  | [] => return ()
  | c :: cs => do
    let p ← resolve_name c
    match p with
      | expr.const n _ => add_ematch_eqn_lemmas_for_core md n >> add_eqn_lemmas_for_core cs
      | _ => fail f! "'{c}' is not a constant"

unsafe def add_eqn_lemmas_for (ids : parse ident*) : smt_tactic Unit :=
  add_eqn_lemmas_for_core reducible ids

unsafe def add_eqn_lemmas (ids : parse ident*) : smt_tactic Unit :=
  add_eqn_lemmas_for ids

private unsafe def add_hinst_lemma_from_name (md : Transparency) (lhs_lemma : Bool) (n : Name) (hs : hinst_lemmas)
    (ref : pexpr) : smt_tactic hinst_lemmas := do
  let p ← resolve_name n
  match p with
    | expr.const n _ =>
      (do
          let h ← hinst_lemma.mk_from_decl_core md n lhs_lemma
          tactic.save_const_type_info n ref
          return <| hs h) <|>
        (do
            let hs₁ ← mk_ematch_eqn_lemmas_for_core md n
            tactic.save_const_type_info n ref
            return <| hs hs₁) <|>
          report_invalid_em_lemma n
    | _ =>
      (do
          let e ← to_expr p
          let h ← hinst_lemma.mk_core md e lhs_lemma
          try (tactic.save_type_info e ref)
          return <| hs h) <|>
        report_invalid_em_lemma n

private unsafe def add_hinst_lemma_from_pexpr (md : Transparency) (lhs_lemma : Bool) (p : pexpr) (hs : hinst_lemmas) :
    smt_tactic hinst_lemmas :=
  match p with
  | expr.const c [] => add_hinst_lemma_from_name md lhs_lemma c hs p
  | expr.local_const c _ _ _ => add_hinst_lemma_from_name md lhs_lemma c hs p
  | _ => do
    let new_e ← to_expr p
    let h ← hinst_lemma.mk_core md new_e lhs_lemma
    return <| hs h

private unsafe def add_hinst_lemmas_from_pexprs (md : Transparency) (lhs_lemma : Bool) :
    List pexpr → hinst_lemmas → smt_tactic hinst_lemmas
  | [], hs => return hs
  | p :: ps, hs => do
    let hs₁ ← add_hinst_lemma_from_pexpr md lhs_lemma p hs
    add_hinst_lemmas_from_pexprs ps hs₁

unsafe def ematch_using (l : parse pexpr_list_or_texpr) : smt_tactic Unit := do
  let hs ← add_hinst_lemmas_from_pexprs reducible false l hinst_lemmas.mk
  smt_tactic.ematch_using hs

/-- Try the given tactic, and do nothing if it fails. -/
unsafe def try (t : itactic) : smt_tactic Unit :=
  smt_tactic.try t

/-- Keep applying the given tactic until it fails. -/
unsafe def iterate (t : itactic) : smt_tactic Unit :=
  smt_tactic.iterate t

/-- Apply the given tactic to all remaining goals. -/
unsafe def all_goals (t : itactic) : smt_tactic Unit :=
  smt_tactic.all_goals t

unsafe def induction (p : parse tactic.interactive.cases_arg_p) (rec_name : parse using_ident)
    (ids : parse with_ident_list) (revert : parse <| (tk "generalizing" *> ident*)?) : smt_tactic Unit :=
  slift (tactic.interactive.induction p rec_name ids revert)

open Tactic

/-- Simplify the target type of the main goal. -/
unsafe def simp (use_iota_eqn : parse <| (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
    (attr_names : parse with_ident_list) (cfg : simp_config_ext := {  }) : smt_tactic Unit :=
  tactic.interactive.simp use_iota_eqn none no_dflt hs attr_names (Loc.ns [none]) cfg

unsafe def dsimp (no_dflt : parse only_flag) (es : parse simp_arg_list) (attr_names : parse with_ident_list) :
    smt_tactic Unit :=
  tactic.interactive.dsimp no_dflt es attr_names (Loc.ns [none])

unsafe def rsimp : smt_tactic Unit := do
  let ccs ← to_cc_state
  _root_.rsimp.rsimplify_goal ccs

unsafe def add_simp_lemmas : smt_tactic Unit :=
  get_hinst_lemmas_for_attr `rsimp_attr >>= add_lemmas

/-- Keep applying heuristic instantiation until the current goal is solved, or it fails. -/
unsafe def eblast : smt_tactic Unit :=
  smt_tactic.eblast

/-- Keep applying heuristic instantiation using the given lemmas until the current goal is solved, or it fails. -/
unsafe def eblast_using (l : parse pexpr_list_or_texpr) : smt_tactic Unit := do
  let hs ← add_hinst_lemmas_from_pexprs reducible false l hinst_lemmas.mk
  smt_tactic.iterate (smt_tactic.ematch_using hs >> smt_tactic.try smt_tactic.close)

unsafe def guard_expr_eq (t : expr) (p : parse <| tk ":=" *> texpr) : smt_tactic Unit := do
  let e ← to_expr p
  guardₓ (expr.alpha_eqv t e)

unsafe def guard_target (p : parse texpr) : smt_tactic Unit := do
  let t ← target
  guard_expr_eq t p

end Interactive

end SmtTactic

