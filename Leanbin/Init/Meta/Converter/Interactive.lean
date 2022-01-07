prelude
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Meta.Converter.Conv

namespace Conv

unsafe def save_info (p : Pos) : conv Unit := do
  let s ← tactic.read
  tactic.save_info_thunk p fun _ => s.to_format tt

unsafe def step {α : Type} (c : conv α) : conv Unit :=
  c >> return ()

unsafe def istep {α : Type} (line0 col0 line col ast : Nat) (c : conv α) : conv Unit :=
  tactic.istep line0 col0 line col ast c

unsafe def execute (c : conv Unit) : tactic Unit :=
  c

unsafe def solve1 (c : conv Unit) : conv Unit :=
  tactic.solve1 $ c >> tactic.try (tactic.any_goals tactic.reflexivity)

namespace Interactive

open Lean

open Lean.Parser

open _Root_.Interactive

open Interactive.Types

open TacticResult

unsafe def itactic : Type :=
  conv Unit

unsafe def skip : conv Unit :=
  conv.skip

unsafe def whnf : conv Unit :=
  conv.whnf

unsafe def dsimp (no_dflt : parse only_flag) (es : parse tactic.simp_arg_list) (attr_names : parse with_ident_list)
    (cfg : Tactic.DsimpConfig := {  }) : conv Unit := do
  let (s, u) ← tactic.mk_simp_set no_dflt attr_names es
  conv.dsimp (some s) u cfg

unsafe def trace_lhs : conv Unit :=
  lhs >>= tactic.trace

unsafe def change (p : parse texpr) : conv Unit :=
  tactic.i_to_expr p >>= conv.change

unsafe def congr : conv Unit :=
  conv.congr

unsafe def funext : conv Unit :=
  conv.funext

private unsafe def is_relation : conv Unit :=
  lhs >>= tactic.relation_lhs_rhs >> return () <|> tactic.fail "current expression is not a relation"

unsafe def to_lhs : conv Unit :=
  is_relation >> congr >> tactic.swap >> skip

unsafe def to_rhs : conv Unit :=
  is_relation >> congr >> skip

unsafe def done : conv Unit :=
  tactic.done

unsafe def find (p : parse parser.pexpr) (c : itactic) : conv Unit := do
  let (r, lhs, _) ← tactic.target_lhs_rhs
  let pat ← tactic.pexpr_to_pattern p
  let s ← simp_lemmas.mk_default
  let st ← tactic.read
  let (found_result, new_lhs, pr) ←
    tactic.ext_simplify_core (success ff st)
        { zeta := ff, beta := ff, singlePass := tt, eta := ff, proj := ff, failIfUnchanged := ff, memoize := ff } s
        (fun u => return u)
        (fun found_result s r p e => do
          let found ← tactic.unwrap found_result
          guardₓ (Not found)
          let matched ← tactic.match_pattern pat e >> return tt <|> return ff
          guardₓ matched
          let res ← tactic.capture (c.convert e r)
          match res with
            | success r s' => return (success tt s', r.fst, some r.snd, ff)
            | exception f p s' => return (exception f p s', e, none, ff))
        (fun a s r p e => tactic.failed) r lhs
  let found ← tactic.unwrap found_result
  when (Not found) $ tactic.fail "find converter failed, pattern was not found"
  update_lhs new_lhs pr

unsafe def for (p : parse parser.pexpr) (occs : parse (list_of small_nat)) (c : itactic) : conv Unit := do
  let (r, lhs, _) ← tactic.target_lhs_rhs
  let pat ← tactic.pexpr_to_pattern p
  let s ← simp_lemmas.mk_default
  let st ← tactic.read
  let (found_result, new_lhs, pr) ←
    tactic.ext_simplify_core (success 1 st)
        { zeta := ff, beta := ff, singlePass := tt, eta := ff, proj := ff, failIfUnchanged := ff, memoize := ff } s
        (fun u => return u)
        (fun found_result s r p e => do
          let i ← tactic.unwrap found_result
          let matched ← tactic.match_pattern pat e >> return tt <|> return ff
          guardₓ matched
          if i ∈ occs then do
              let res ← tactic.capture (c.convert e r)
              match res with
                | success r s' => return (success (i + 1) s', r.fst, some r.snd, tt)
                | exception f p s' => return (exception f p s', e, none, tt)
            else do
              let st ← tactic.read
              return (success (i + 1) st, e, none, tt))
        (fun a s r p e => tactic.failed) r lhs
  tactic.unwrap found_result
  update_lhs new_lhs pr

unsafe def simp (no_dflt : parse only_flag) (hs : parse tactic.simp_arg_list) (attr_names : parse with_ident_list)
    (cfg : tactic.simp_config_ext := {  }) : conv Unit := do
  let (s, u) ← tactic.mk_simp_set no_dflt attr_names hs
  let (r, lhs, rhs) ← tactic.target_lhs_rhs
  let (new_lhs, pr, lms) ← tactic.simplify s u lhs cfg.to_simp_config r cfg.discharger
  update_lhs new_lhs pr
  return ()

unsafe def guard_lhs (p : parse texpr) : tactic Unit := do
  let t ← lhs
  tactic.interactive.guard_expr_eq t p

section Rw

open tactic.interactive (rw_rules rw_rule get_rule_eqn_lemmas to_expr')

open tactic (RewriteCfg)

private unsafe def rw_lhs (h : expr) (cfg : rewrite_cfg) : conv Unit := do
  let l ← conv.lhs
  let (new_lhs, prf, _) ← tactic.rewrite h l cfg
  update_lhs new_lhs prf

private unsafe def rw_core (rs : List rw_rule) (cfg : rewrite_cfg) : conv Unit :=
  rs.mmap' $ fun r => do
    save_info r.pos
    let eq_lemmas ← get_rule_eqn_lemmas r
    orelse'
        (do
          let h ← to_expr' r.rule
          rw_lhs h { cfg with symm := r.symm })
        (eq_lemmas.mfirst $ fun n => do
          let e ← tactic.mk_const n
          rw_lhs e { cfg with symm := r.symm })
        eq_lemmas.empty

unsafe def rewrite (q : parse rw_rules) (cfg : rewrite_cfg := {  }) : conv Unit :=
  rw_core q.rules cfg

unsafe def rw (q : parse rw_rules) (cfg : rewrite_cfg := {  }) : conv Unit :=
  rw_core q.rules cfg

end Rw

end Interactive

end Conv

namespace Tactic

namespace Interactive

open Lean

open Lean.Parser

open _Root_.Interactive

open Interactive.Types

open Tactic

local postfix:9001 "?" => optionalₓ

private unsafe def conv_at (h_name : Name) (c : conv Unit) : tactic Unit := do
  let h ← get_local h_name
  let h_type ← infer_type h
  let (new_h_type, pr) ← c.convert h_type
  replace_hyp h new_h_type pr
  return ()

private unsafe def conv_target (c : conv Unit) : tactic Unit := do
  let t ← target
  let (new_t, pr) ← c.convert t
  replace_target new_t pr
  try tactic.triv
  try (tactic.reflexivity reducible)

unsafe def conv (loc : parse (tk "at" *> ident)?) (p : parse (tk "in" *> parser.pexpr)?)
    (c : conv.interactive.itactic) : tactic Unit := do
  let c :=
    match p with
    | some p => _root_.conv.interactive.find p c
    | none => c
  match loc with
    | some h => conv_at h c
    | none => conv_target c

end Interactive

end Tactic

