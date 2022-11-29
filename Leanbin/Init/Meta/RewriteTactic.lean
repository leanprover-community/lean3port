/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.RelationTactics
import Leanbin.Init.Meta.Occurrences

namespace Tactic

def IdTag.rw : Unit :=
  ()
#align tactic.id_tag.rw Tactic.IdTag.rw

/-- Configuration options for the `rewrite` tactic. -/
structure RewriteCfg extends ApplyCfg where
  md := reducible
  symm := false
  occs := Occurrences.all
#align tactic.rewrite_cfg Tactic.RewriteCfg

/-- Rewrite the expression `e` using `h`.
    The unification is performed using the transparency mode in `cfg`.
    If `cfg.approx` is `tt`, then fallback to first-order unification, 
    and approximate context during unification.
    `cfg.new_goals` specifies which unassigned metavariables become new goals, 
    and their order.
    If `cfg.instances` is `tt`, then use type class resolution to instantiate 
    unassigned meta-variables.
    The fields `cfg.auto_param` and `cfg.opt_param` are ignored by this tactic 
    (See `tactic.rewrite`).
    It a triple `(new_e, prf, metas)` where `prf : e = new_e`, and `metas` 
    is a list of all introduced meta variables,
    even the assigned ones.

    TODO(Leo): improve documentation and explain symm/occs -/
unsafe axiom rewrite_core (h : expr) (e : expr) (cfg : RewriteCfg := {  }) :
    tactic (expr × expr × List expr)
#align tactic.rewrite_core tactic.rewrite_core

unsafe def rewrite (h : expr) (e : expr) (cfg : RewriteCfg := {  }) :
    tactic (expr × expr × List expr) := do
  let (new_t, prf, metas) ← rewrite_core h e cfg
  try_apply_opt_auto_param cfg metas
  return (new_t, prf, metas)
#align tactic.rewrite tactic.rewrite

unsafe def rewrite_target (h : expr) (cfg : RewriteCfg := {  }) : tactic Unit := do
  let t ← target
  let (new_t, prf, _) ← rewrite h t cfg
  replace_target new_t prf `` id_tag.rw
#align tactic.rewrite_target tactic.rewrite_target

unsafe def rewrite_hyp (h : expr) (hyp : expr) (cfg : RewriteCfg := {  }) : tactic expr := do
  let hyp_type ← infer_type hyp
  let (new_hyp_type, prf, _) ← rewrite h hyp_type cfg
  replace_hyp hyp new_hyp_type prf `` id_tag.rw
#align tactic.rewrite_hyp tactic.rewrite_hyp

end Tactic

