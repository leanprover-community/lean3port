/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.TypeContext
import Leanbin.Init.Meta.RewriteTactic
import Leanbin.Init.Meta.SimpTactic
import Leanbin.Init.Meta.Smt.CongruenceClosure
import Leanbin.Init.Control.Combinators
import Leanbin.Init.Meta.InteractiveBase
import Leanbin.Init.Meta.Derive
import Leanbin.Init.Meta.MatchTactic
import Leanbin.Init.Meta.CongrTactic
import Leanbin.Init.Meta.CaseTag

open Lean

open Lean.Parser

open Native

-- ./././Mathport/Syntax/Translate/Command.lean:619:29: warning: unsupported: precedence command
-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

-- mathport name: «expr *»
local postfix:1024 "*" => many

namespace Tactic

-- allows metavars
unsafe def i_to_expr (q : pexpr) : tactic expr :=
  to_expr q true

-- allow metavars and no subgoals
unsafe def i_to_expr_no_subgoals (q : pexpr) : tactic expr :=
  to_expr q true false

-- doesn't allows metavars
unsafe def i_to_expr_strict (q : pexpr) : tactic expr :=
  to_expr q false

/- Auxiliary version of i_to_expr for apply-like tactics.
   This is a workaround for comment
      https://github.com/leanprover/lean/issues/1342#issuecomment-307912291
   at issue #1342.

   In interactive mode, given a tactic

        apply f

   we want the apply tactic to create all metavariables. The following
   definition will return `@f` for `f`. That is, it will **not** create
   metavariables for implicit arguments.

   Before we added `i_to_expr_for_apply`, the tactic

       apply le_antisymm

   would first elaborate `le_antisymm`, and create

       @le_antisymm ?m_1 ?m_2 ?m_3 ?m_4

   The type class resolution problem
        ?m_2 : weak_order ?m_1
   by the elaborator since ?m_1 is not assigned yet, and the problem is
   discarded.

   Then, we would invoke `apply_core`, which would create two
   new metavariables for the explicit arguments, and try to unify the resulting
   type with the current target. After the unification,
   the metavariables ?m_1, ?m_3 and ?m_4 are assigned, but we lost
   the information about the pending type class resolution problem.

   With `i_to_expr_for_apply`, `le_antisymm` is elaborate into `@le_antisymm`,
   the apply_core tactic creates all metavariables, and solves the ones that
   can be solved by type class resolution.

   Another possible fix: we modify the elaborator to return pending
   type class resolution problems, and store them in the tactic_state.
-/
unsafe def i_to_expr_for_apply (q : pexpr) : tactic expr :=
  let aux (n : Name) : tactic expr := do
    let p ← resolve_name n
    match p with
      | expr.const c [] => do
        let r ← mk_const c
        save_type_info r q
        return r
      | _ => i_to_expr p
  match q with
  | expr.const c [] => aux c
  | expr.local_const c _ _ _ => aux c
  | _ => i_to_expr q

namespace Interactive

open _Root_.Interactive Interactive.Types Expr

/-- itactic: parse a nested "interactive" tactic. That is, parse
  `{` tactic `}`
-/
unsafe def itactic : Type :=
  tactic Unit

unsafe def propagate_tags (tac : itactic) : tactic Unit := do
  let tag ← get_main_tag
  if tag = [] then tac
    else
      focus1 <| do
        tac
        let gs ← get_goals
        when (bnot gs) <| do
            let new_tag ← get_main_tag
            when new_tag <| with_enable_tags (set_main_tag tag)

unsafe def concat_tags (tac : tactic (List (Name × expr))) : tactic Unit :=
  mcond tags_enabled
    (do
      let in_tag ← get_main_tag
      let r ← tac
      let r
        ←-- remove assigned metavars
              r.mfilter
            fun ⟨n, m⟩ => bnot <$> is_assigned m
      match r with
        | [(_, m)] => set_tag m in_tag
        |-- if there is only new subgoal, we just propagate `in_tag`
          _ =>
          r fun ⟨n, m⟩ => set_tag m (n :: in_tag))
    (tac >> skip)

/--
If the current goal is a Pi/forall `∀ x : t, u` (resp. `let x := t in u`) then `intro` puts `x : t` (resp. `x := t`) in the local context. The new subgoal target is `u`.

If the goal is an arrow `t → u`, then it puts `h : t` in the local context and the new goal target is `u`.

If the goal is neither a Pi/forall nor begins with a let binder, the tactic `intro` applies the tactic `whnf` until an introduction can be applied or the goal is not head reducible. In the latter case, the tactic fails.
-/
unsafe def intro : parse ident_ ? → tactic Unit
  | none => propagate_tags (intro1 >> skip)
  | some h => propagate_tags (tactic.intro h >> skip)

/--
Similar to `intro` tactic. The tactic `intros` will keep introducing new hypotheses until the goal target is not a Pi/forall or let binder.

The variant `intros h₁ ... hₙ` introduces `n` new hypotheses using the given identifiers to name them.
-/
unsafe def intros : parse ident_* → tactic Unit
  | [] => propagate_tags (tactic.intros >> skip)
  | hs => propagate_tags (intro_lst hs >> skip)

/--
The tactic `introv` allows the user to automatically introduce the variables of a theorem and explicitly name the hypotheses involved. The given names are used to name non-dependent hypotheses.

Examples:
```
example : ∀ a b : nat, a = b → b = a :=
begin
  introv h,
  exact h.symm
end
```
The state after `introv h` is
```
a b : ℕ,
h : a = b
⊢ b = a
```

```
example : ∀ a b : nat, a = b → ∀ c, b = c → a = c :=
begin
  introv h₁ h₂,
  exact h₁.trans h₂
end
```
The state after `introv h₁ h₂` is
```
a b : ℕ,
h₁ : a = b,
c : ℕ,
h₂ : b = c
⊢ a = c
```
-/
unsafe def introv (ns : parse ident_*) : tactic Unit :=
  propagate_tags (tactic.introv ns >> return ())

/-- Parse a current name and new name for `rename`. -/
private unsafe def rename_arg_parser : parser (Name × Name) :=
  Prod.mk <$> ident <*> (optionalₓ (tk "->") *> ident)

/-- Parse the arguments of `rename`. -/
private unsafe def rename_args_parser : parser (List (Name × Name)) :=
  Functor.map (fun x => [x]) rename_arg_parser <|> tk "[" *> sep_by (tk ",") rename_arg_parser <* tk "]"

/-- Rename one or more local hypotheses. The renamings are given as follows:

```
rename x y             -- rename x to y
rename x → y           -- ditto
rename [x y, a b]      -- rename x to y and a to b
rename [x → y, a → b]  -- ditto
```

Note that if there are multiple hypotheses called `x` in the context, then
`rename x y` will rename *all* of them. If you want to rename only one, use
`dedup` first.
-/
unsafe def rename (renames : parse rename_args_parser) : tactic Unit :=
  propagate_tags <| tactic.rename_many <| native.rb_map.of_list renames

/--
The `apply` tactic tries to match the current goal against the conclusion of the type of term. The argument term should be a term well-formed in the local context of the main goal. If it succeeds, then the tactic returns as many subgoals as the number of premises that have not been fixed by type inference or type class resolution. Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution, and first-order unification with dependent types.
-/
unsafe def apply (q : parse texpr) : tactic Unit :=
  concat_tags do
    let h ← i_to_expr_for_apply q
    tactic.apply h

/-- Similar to the `apply` tactic, but does not reorder goals.
-/
unsafe def fapply (q : parse texpr) : tactic Unit :=
  concat_tags (i_to_expr_for_apply q >>= tactic.fapply)

/--
Similar to the `apply` tactic, but only creates subgoals for non-dependent premises that have not been fixed by type inference or type class resolution.
-/
unsafe def eapply (q : parse texpr) : tactic Unit :=
  concat_tags (i_to_expr_for_apply q >>= tactic.eapply)

/-- Similar to the `apply` tactic, but allows the user to provide a `apply_cfg` configuration object.
-/
unsafe def apply_with (q : parse parser.pexpr) (cfg : ApplyCfg) : tactic Unit :=
  concat_tags do
    let e ← i_to_expr_for_apply q
    tactic.apply e cfg

/-- Similar to the `apply` tactic, but uses matching instead of unification.
`apply_match t` is equivalent to `apply_with t {unify := ff}`
-/
unsafe def mapply (q : parse texpr) : tactic Unit :=
  concat_tags do
    let e ← i_to_expr_for_apply q
    tactic.apply e { unify := ff }

/-- This tactic tries to close the main goal `... ⊢ t` by generating a term of type `t` using type class resolution.
-/
unsafe def apply_instance : tactic Unit :=
  tactic.apply_instance

/--
This tactic behaves like `exact`, but with a big difference: the user can put underscores `_` in the expression as placeholders for holes that need to be filled, and `refine` will generate as many subgoals as there are holes.

Note that some holes may be implicit. The type of each hole must either be synthesized by the system or declared by an explicit type ascription like `(_ : nat → Prop)`.
-/
unsafe def refine (q : parse texpr) : tactic Unit :=
  tactic.refine q

/--
This tactic looks in the local context for a hypothesis whose type is equal to the goal target. If it finds one, it uses it to prove the goal, and otherwise it fails.
-/
unsafe def assumption : tactic Unit :=
  tactic.assumption

/-- Try to apply `assumption` to all goals. -/
unsafe def assumption' : tactic Unit :=
  tactic.any_goals' tactic.assumption

private unsafe def change_core (e : expr) : Option expr → tactic Unit
  | none => tactic.change e
  | some h => do
    let num_reverted : ℕ ← revert h
    let expr.pi n bi d b ← target
    tactic.change <| expr.pi n bi e b
    intron num_reverted

/--
`change u` replaces the target `t` of the main goal to `u` provided that `t` is well formed with respect to the local context of the main goal and `t` and `u` are definitionally equal.

`change u at h` will change a local hypothesis to `u`.

`change t with u at h1 h2 ...` will replace `t` with `u` in all the supplied hypotheses (or `*`), or in the goal if no `at` clause is specified, provided that `t` and `u` are definitionally equal.
-/
unsafe def change (q : parse texpr) : parse (tk "with" *> texpr)? → parse location → tactic Unit
  | none, loc.ns [none] => do
    let e ← i_to_expr q
    change_core e none
  | none, loc.ns [some h] => do
    let eq ← i_to_expr q
    let eh ← get_local h
    change_core Eq (some eh)
  | none, _ => fail "change-at does not support multiple locations"
  | some w, l => do
    let u ← mk_meta_univ
    let ty ← mk_meta_var (sort u)
    let eq ← i_to_expr (pquote.1 (%%ₓq : %%ₓty))
    let ew ← i_to_expr (pquote.1 (%%ₓw : %%ₓty))
    let repl := fun e : expr => e.replace fun a n => if a = Eq then some ew else none
    l
        (fun h => do
          let e ← infer_type h
          change_core (repl e) (some h))
        do
        let g ← target
        change_core (repl g) none

/--
This tactic provides an exact proof term to solve the main goal. If `t` is the goal and `p` is a term of type `u` then `exact p` succeeds if and only if `t` and `u` can be unified.
-/
unsafe def exact (q : parse texpr) : tactic Unit := do
  let tgt : expr ← target
  i_to_expr_strict (pquote.1 (%%ₓq : %%ₓtgt)) >>= tactic.exact

/-- Like `exact`, but takes a list of terms and checks that all goals are discharged after the tactic.
-/
unsafe def exacts : parse pexpr_list_or_texpr → tactic Unit
  | [] => done
  | t :: ts => exact t >> exacts ts

/-- A synonym for `exact` that allows writing `have/suffices/show ..., from ...` in tactic mode.
-/
unsafe def from :=
  exact

/--
`revert h₁ ... hₙ` applies to any goal with hypotheses `h₁` ... `hₙ`. It moves the hypotheses and their dependencies to the target of the goal. This tactic is the inverse of `intro`.
-/
unsafe def revert (ids : parse ident*) : tactic Unit :=
  propagate_tags do
    let hs ← mmapₓ tactic.get_local ids
    revert_lst hs
    skip

private unsafe def resolve_name' (n : Name) : tactic expr := do
  let p ← resolve_name n
  match p with
    | expr.const n _ => mk_const n
    |-- create metavars for universe levels
      _ =>
      i_to_expr p

/- Version of to_expr that tries to bypass the elaborator if `p` is just a constant or local constant.
   This is not an optimization, by skipping the elaborator we make sure that no unwanted resolution is used.
   Example: the elaborator will force any unassigned ?A that must have be an instance of (has_one ?A) to nat.
   Remark: another benefit is that auxiliary temporary metavariables do not appear in error messages. -/
unsafe def to_expr' (p : pexpr) : tactic expr :=
  match p with
  | const c [] => do
    let new_e ← resolve_name' c
    save_type_info new_e p
    return new_e
  | local_const c _ _ _ => do
    let new_e ← resolve_name' c
    save_type_info new_e p
    return new_e
  | _ => i_to_expr p

unsafe structure rw_rule where
  Pos : Pos
  symm : Bool
  rule : pexpr
  deriving has_reflect

unsafe def get_rule_eqn_lemmas (r : rw_rule) : tactic (List Name) :=
  let aux (n : Name) : tactic (List Name) :=
    (-- unpack local refs
      do
        let p ← resolve_name n
        let e := p.erase_annotations.get_app_fn.erase_annotations
        match e with
          | const n _ => get_eqn_lemmas_for tt n
          | _ => return []) <|>
      return []
  match r.rule with
  | const n _ => aux n
  | local_const n _ _ _ => aux n
  | _ => return []

-- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `eq_lemmas
private unsafe def rw_goal (cfg : RewriteCfg) (rs : List rw_rule) : tactic Unit :=
  rs.mmap' fun r => do
    save_info r
    let eq_lemmas ← get_rule_eqn_lemmas r
    orelse'
        (do
          let e ← to_expr' r
          rewrite_target e { cfg with symm := r })
        (eq_lemmas fun n => do
          let e ← mk_const n
          rewrite_target e { cfg with symm := r })
        (eq_lemmas eq_lemmas.empty)

private unsafe def uses_hyp (e : expr) (h : expr) : Bool :=
  (e.fold false) fun t _ r => r || toBool (t = h)

-- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `eq_lemmas
private unsafe def rw_hyp (cfg : RewriteCfg) : List rw_rule → expr → tactic Unit
  | [], hyp => skip
  | r :: rs, hyp => do
    save_info r
    let eq_lemmas ← get_rule_eqn_lemmas r
    orelse'
        (do
          let e ← to_expr' r
          (if uses_hyp e hyp then pure e else rewrite_hyp e hyp { cfg with symm := r }) >>= rw_hyp rs)
        (eq_lemmas fun n => do
          let e ← mk_const n
          rewrite_hyp e hyp { cfg with symm := r } >>= rw_hyp rs)
        (eq_lemmas eq_lemmas.empty)

unsafe def rw_rule_p (ep : parser pexpr) : parser rw_rule :=
  rw_rule.mk <$> cur_pos <*> Option.isSome <$> (with_desc "←" (tk "←" <|> tk "<-"))? <*> ep

unsafe structure rw_rules_t where
  rules : List rw_rule
  end_pos : Option Pos
  deriving has_reflect

-- accepts the same content as `pexpr_list_or_texpr`, but with correct goal info pos annotations
unsafe def rw_rules : parser rw_rules_t :=
  tk "[" *> rw_rules_t.mk <$> sep_by (skip_info (tk ",")) (set_goal_info_pos <| rw_rule_p (parser.pexpr 0)) <*>
      (some <$> cur_pos <* set_goal_info_pos (tk "]")) <|>
    rw_rules_t.mk <$> List.ret <$> rw_rule_p texpr <*> return none

private unsafe def rw_core (rs : parse rw_rules) (loca : parse location) (cfg : RewriteCfg) : tactic Unit :=
  ((match loca with
      | loc.wildcard => loca.try_apply (rw_hyp cfg rs.rules) (rw_goal cfg rs.rules)
      | _ => loca.apply (rw_hyp cfg rs.rules) (rw_goal cfg rs.rules)) >>
      try (reflexivity reducible)) >>
    (returnopt rs.end_pos >>= save_info <|> skip)

/--
`rewrite e` applies identity `e` as a rewrite rule to the target of the main goal. If `e` is preceded by left arrow (`←` or `<-`), the rewrite is applied in the reverse direction. If `e` is a defined constant, then the equational lemmas associated with `e` are used. This provides a convenient way to unfold `e`.

`rewrite [e₁, ..., eₙ]` applies the given rules sequentially.

`rewrite e at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a list of hypotheses in the local context. In the latter case, a turnstile `⊢` or `|-` can also be used, to signify the target of the goal.
-/
unsafe def rewrite (q : parse rw_rules) (l : parse location) (cfg : RewriteCfg := {  }) : tactic Unit :=
  propagate_tags (rw_core q l cfg)

/-- An abbreviation for `rewrite`.
-/
unsafe def rw (q : parse rw_rules) (l : parse location) (cfg : RewriteCfg := {  }) : tactic Unit :=
  propagate_tags (rw_core q l cfg)

/-- `rewrite` followed by `assumption`.
-/
unsafe def rwa (q : parse rw_rules) (l : parse location) (cfg : RewriteCfg := {  }) : tactic Unit :=
  rewrite q l cfg >> try assumption

/-- A variant of `rewrite` that uses the unifier more aggressively, unfolding semireducible definitions.
-/
unsafe def erewrite (q : parse rw_rules) (l : parse location) (cfg : RewriteCfg := { md := semireducible }) :
    tactic Unit :=
  propagate_tags (rw_core q l cfg)

/-- An abbreviation for `erewrite`.
-/
unsafe def erw (q : parse rw_rules) (l : parse location) (cfg : RewriteCfg := { md := semireducible }) : tactic Unit :=
  propagate_tags (rw_core q l cfg)

/-- Returns the unique names of all hypotheses (local constants) in the context.
-/
private unsafe def hyp_unique_names : tactic name_set := do
  let ctx ← local_context
  pure <| ctx (fun r h => r h) mk_name_set

/-- Returns all hypotheses (local constants) from the context except those whose
unique names are in `hyp_uids`.
-/
private unsafe def hyps_except (hyp_uids : name_set) : tactic (List expr) := do
  let ctx ← local_context
  pure <| ctx fun h : expr => ¬hyp_uids h

/-- Apply `t` to the main goal and revert any new hypothesis in the generated goals.
If `t` is a supported tactic or chain of supported tactics (e.g. `induction`,
`cases`, `apply`, `constructor`), the generated goals are also tagged with case
tags. You can then use `case` to focus such tagged goals.

Two typical uses of `with_cases`:

1. Applying a custom eliminator:

   ```
   lemma my_nat_rec :
     ∀ n {P : ℕ → Prop} (zero : P 0) (succ : ∀ n, P n → P (n + 1)), P n := ...

   example (n : ℕ) : n = n :=
   begin
     with_cases { apply my_nat_rec n },
     case zero { refl },
     case succ : m ih { refl }
   end
   ```

2. Enabling the use of `case` after a chain of case-splitting tactics:

   ```
   example (n m : ℕ) : unit :=
   begin
     with_cases { cases n; induction m },
     case nat.zero nat.zero { exact () },
     case nat.zero nat.succ : k { exact () },
     case nat.succ nat.zero : i { exact () },
     case nat.succ nat.succ : k i ih_i { exact () }
   end
   ```
-/
unsafe def with_cases (t : itactic) : tactic Unit :=
  with_enable_tags <|
    focus1 <| do
      let input_hyp_uids ← hyp_unique_names
      t
      all_goals' <| do
          let in_tag ← get_main_tag
          let new_hyps ← hyps_except input_hyp_uids
          let n ← revert_lst new_hyps
          set_main_tag (case_tag.from_tag_pi in_tag n).render

private unsafe def generalize_arg_p_aux : pexpr → parser (pexpr × Name)
  | app (app (macro _ [const `eq _]) h) (local_const x _ _ _) => pure (h, x)
  | _ => fail "parse error"

private unsafe def generalize_arg_p : parser (pexpr × Name) :=
  with_desc "expr = id" <| parser.pexpr 0 >>= generalize_arg_p_aux

/-- `generalize : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of the same type.

`generalize h : e = x` in addition registers the hypothesis `h : e = x`.
-/
unsafe def generalize (h : parse ident ?) (_ : parse <| tk ":") (p : parse generalize_arg_p) : tactic Unit :=
  propagate_tags <| do
    let (p, x) := p
    let e ← i_to_expr p
    let some h ← pure h | (tactic.generalize e x >> intro1) >> skip
    let tgt ← target
    let tgt' ←
      (-- if generalizing fails, fall back to not replacing anything
          do
            let ⟨tgt', _⟩ ← solve_aux tgt (tactic.generalize e x >> target)
            to_expr (pquote.1 (∀ x, (%%ₓe) = x → %%ₓtgt' 0 1))) <|>
          to_expr (pquote.1 (∀ x, (%%ₓe) = x → %%ₓtgt))
    let t ← assert h tgt'
    swap
    exact (pquote.1 ((%%ₓt) (%%ₓe) rfl))
    intro x
    intro h

unsafe def cases_arg_p : parser (Option Name × pexpr) :=
  with_desc "(id :)? expr" <| do
    let t ← texpr
    match t with
      | local_const x _ _ _ =>
        (tk ":" *> do
            let t ← texpr
            pure (some x, t)) <|>
          pure (none, t)
      | _ => pure (none, t)

/-- Updates the tags of new subgoals produced by `cases` or `induction`. `in_tag`
  is the initial tag, i.e. the tag of the goal on which `cases`/`induction` was
  applied. `rs` should contain, for each subgoal, the constructor name
  associated with that goal and the hypotheses that were introduced.
-/
private unsafe def set_cases_tags (in_tag : Tag) (rs : List (Name × List expr)) : tactic Unit := do
  let gs ← get_goals
  match gs with
    |-- if only one goal was produced, we should not make the tag longer
      [g] =>
      set_tag g in_tag
    | _ =>
      let tgs : List (Name × List expr × expr) := rs (fun ⟨n, new_hyps⟩ g => ⟨n, new_hyps, g⟩) gs
      tgs fun ⟨n, new_hyps, g⟩ =>
        with_enable_tags <| set_tag g <| (case_tag.from_tag_hyps (n :: in_tag) (new_hyps expr.local_uniq_name)).render

-- ./././Mathport/Syntax/Translate/Command.lean:619:29: warning: unsupported: precedence command
/--
Assuming `x` is a variable in the local context with an inductive type, `induction x` applies induction on `x` to the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor and an inductive hypothesis is added for each recursive argument to the constructor. If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward, so that the inductive hypothesis incorporates that hypothesis as well.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `induction n` produces one goal with hypothesis `h : P 0` and target `Q 0`, and one goal with hypotheses `h : P (nat.succ a)` and `ih₁ : P a → Q a` and target `Q (nat.succ a)`. Here the names `a` and `ih₁` ire chosen automatically.

`induction e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then performs induction on the resulting variable.

`induction e with y₁ ... yₙ`, where `e` is a variable or an expression, specifies that the sequence of names `y₁ ... yₙ` should be used for the arguments to the constructors and inductive hypotheses, including implicit arguments. If the list does not include enough names for all of the arguments, additional names are generated automatically. If too many names are given, the extra ones are ignored. Underscores can be used in the list, in which case the corresponding names are generated automatically. Note that for long sequences of names, the `case` tactic provides a more convenient naming mechanism.

`induction e using r` allows the user to specify the principle of induction that should be used. Here `r` should be a theorem whose result type must be of the form `C t`, where `C` is a bound variable and `t` is a (possibly empty) sequence of bound variables

`induction e generalizing z₁ ... zₙ`, where `z₁ ... zₙ` are variables in the local context, generalizes over `z₁ ... zₙ` before applying the induction but then introduces them in each goal. In other words, the net effect is that each inductive hypothesis is generalized.

`induction h : t` will introduce an equality of the form `h : t = C x y`, asserting that the input term is equal to the current constructor case, to the context.
-/
unsafe def induction (hp : parse cases_arg_p) (rec_name : parse using_ident) (ids : parse with_ident_list)
    (revert : parse <| (tk "generalizing" *> ident*)?) : tactic Unit := do
  let in_tag ← get_main_tag
  focus1 <| do
      let e
        ←-- process `h : t` case
          match hp with
          | (some h, p) => do
            let x ← get_unused_name
            generalize h () (p, x)
            get_local x
          | (none, p) => i_to_expr p
      let e
        ←-- generalize major premise
            if e then pure e
          else tactic.generalize e >> intro1
      let-- generalize major premise args
        (e, newvars, locals)
        ←
        do
          let none ← pure rec_name | pure (e, [], [])
          let t ← infer_type e
          let t ← whnf_ginductive t
          let const n _ ← pure t | pure (e, [], [])
          let env ← get_env
          let tt ← pure <| env n | pure (e, [], [])
          let (locals, nonlocals) := (t <| env n).partition fun arg : expr => arg
          let _ :: _ ← pure nonlocals | pure (e, [], [])
          let n ← tactic.revert e
          let newvars ←
            nonlocals fun arg => do
                let n ← revert_kdeps arg
                tactic.generalize arg
                let h ← intro1
                intron n
                let-- now try to clear hypotheses that may have been abstracted away
                locals := arg [] fun e _ acc => if e then e :: Acc else Acc
                locals (try ∘ clear)
                pure h
          intron (n - 1)
          let e ← intro1
          pure (e, newvars, locals)
      let to_generalize ←
        (-- revert `generalizing` params (and their dependencies, if any)
                revert
                []).mmap
            tactic.get_local
      let num_generalized ← revert_lst to_generalize
      let rs
        ←-- perform the induction
            tactic.induction
            e ids rec_name
      let gen_hyps
        ←-- re-introduce the generalized hypotheses
            all_goals <|
            do
            let new_hyps ← intron' num_generalized
            clear_lst (newvars local_pp_name)
            (e :: locals).mmap' (try ∘ clear)
            pure new_hyps
      set_cases_tags in_tag <|
          @List.map₂ₓ (Name × List expr × List (Name × expr)) _ (Name × List expr)
            (fun ⟨n, hyps, _⟩ gen_hyps => ⟨n, hyps ++ gen_hyps⟩) rs gen_hyps

open CaseTag.MatchResult

private unsafe def goals_with_matching_tag (ns : List Name) :
    tactic (List (expr × case_tag) × List (expr × case_tag)) := do
  let gs ← get_goals
  let (gs : List (expr × tag)) ←
    gs.mmap fun g => do
        let t ← get_tag g
        pure (g, t)
  pure <|
      gs
        (fun ⟨g, t⟩ ⟨exact_matches, suffix_matches⟩ =>
          match case_tag.parse t with
          | none => ⟨exact_matches, suffix_matches⟩
          | some t =>
            match case_tag.match_tag ns t with
            | exact_match => ⟨⟨g, t⟩ :: exact_matches, suffix_matches⟩
            | fuzzy_match => ⟨exact_matches, ⟨g, t⟩ :: suffix_matches⟩
            | no_match => ⟨exact_matches, suffix_matches⟩)
        ([], [])

private unsafe def goal_with_matching_tag (ns : List Name) : tactic (expr × case_tag) := do
  let ⟨exact_matches, suffix_matches⟩ ← goals_with_matching_tag ns
  match exact_matches, suffix_matches with
    | [], [] => fail f! "Invalid `case`: there is no goal tagged with suffix {ns}."
    | [], [g] => pure g
    | [], _ =>
      let tags : List (List Name) := suffix_matches fun ⟨_, t⟩ => t
      fail
        f! "Invalid `case`: there is more than one goal tagged with suffix {ns }.
          Matching tags: {tags}"
    | [g], _ => pure g
    | _, _ => fail f! "Invalid `case`: there is more than one goal tagged with tag {ns}."

unsafe def case_arg_parser : lean.parser (List Name × Option (List Name)) :=
  Prod.mk <$> ident_* <*> (tk ":" *> ident_*)?

unsafe def case_parser : lean.parser (List (List Name × Option (List Name))) :=
  list_of case_arg_parser <|> Functor.map (fun x => [x]) case_arg_parser

/-
TODO `case` could be generalised to work with zero names as well. The form

  case : x y z { ... }

would select the first goal (or the first goal with a case tag), renaming
hypotheses to `x, y, z`. The renaming functionality would be available only if
the goal has a case tag.
-/
/-- Focuses on a goal ('case') generated by `induction`, `cases` or `with_cases`.

The goal is selected by giving one or more names which must match exactly one
goal. A goal is matched if the given names are a suffix of its goal tag.
Additionally, each name in the sequence can be abbreviated to a suffix of the
corresponding name in the goal tag. Thus, a goal with tag
```
nat.zero, list.nil
```
can be selected with any of these invocations (among others):
```
case nat.zero list.nil {...}
case nat.zero nil      {...}
case zero     nil      {...}
case          nil      {...}
```

Additionally, the form
```
case C : N₀ ... Nₙ {...}
```
can be used to rename hypotheses introduced by the preceding
`cases`/`induction`/`with_cases`, using the names `Nᵢ`. For example:
```
example (xs : list ℕ) : xs = xs :=
begin
  induction xs,
  case nil { reflexivity },
  case cons : x xs ih {
    -- x : ℕ, xs : list ℕ, ih : xs = xs
    reflexivity }
end
```

Note that this renaming functionality only work reliably *directly after* an
`induction`/`cases`/`with_cases`. If you need to perform additional work after
an `induction` or `cases` (e.g. introduce hypotheses in all goals), use
`with_cases`.

Multiple cases can be handled by the same tactic block with
```
case [A : N₀ ... Nₙ, B : M₀ ... Mₙ] {...}
```
-/
unsafe def case (args : parse case_parser) (tac : itactic) : tactic Unit := do
  let target_goals ←
    args.mmap fun ⟨ns, ids⟩ => do
        let ⟨goal, tag⟩ ← goal_with_matching_tag ns
        let ids := ids.getOrElse []
        let num_ids := ids.length
        let goals ← get_goals
        let other_goals := goals.filter (· ≠ goal)
        set_goals [goal]
        match tag with
          | case_tag.pi _ num_args => do
            intro_lst ids
            when (num_ids < num_args) <| intron (num_args - num_ids)
          | case_tag.hyps _ new_hyp_names => do
            let num_new_hyps := new_hyp_names
            when (num_ids > num_new_hyps) <|
                fail
                  f! "Invalid `case`: You gave {num_ids } names, but the case introduces {num_new_hyps} new hypotheses."
            let renamings := native.rb_map.of_list (new_hyp_names ids)
            propagate_tags <| tactic.rename_many renamings tt tt
        let goals ← get_goals
        set_goals other_goals
        match goals with
          | [g] => return g
          | _ => fail "Unexpected goals introduced by renaming"
  let remaining_goals ← get_goals
  set_goals target_goals
  tac
  let unsolved_goals ← get_goals
  match unsolved_goals with
    | [] => set_goals remaining_goals
    | _ => fail "case tactic failed, focused goals have not been solved"

/--
Assuming `x` is a variable in the local context with an inductive type, `destruct x` splits the main goal, producing one goal for each constructor of the inductive type, in which `x` is assumed to be a general instance of that constructor. In contrast to `cases`, the local context is unchanged, i.e. no elements are reverted or introduced.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `destruct n` produces one goal with target `n = 0 → Q n`, and one goal with target `∀ (a : ℕ), (λ (w : ℕ), n = w → Q n) (nat.succ a)`. Here the name `a` is chosen automatically.
-/
unsafe def destruct (p : parse texpr) : tactic Unit :=
  i_to_expr p >>= tactic.destruct

unsafe def cases_core (e : expr) (ids : List Name := []) : tactic Unit := do
  let in_tag ← get_main_tag
  focus1 <| do
      let rs ← tactic.cases e ids
      set_cases_tags in_tag rs

/--
Assuming `x` is a variable in the local context with an inductive type, `cases x` splits the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor. If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward, so that the case split affects that hypothesis as well.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `cases n` produces one goal with hypothesis `h : P 0` and target `Q 0`, and one goal with hypothesis `h : P (nat.succ a)` and target `Q (nat.succ a)`. Here the name `a` is chosen automatically.

`cases e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then cases on the resulting variable.

`cases e with y₁ ... yₙ`, where `e` is a variable or an expression, specifies that the sequence of names `y₁ ... yₙ` should be used for the arguments to the constructors, including implicit arguments. If the list does not include enough names for all of the arguments, additional names are generated automatically. If too many names are given, the extra ones are ignored. Underscores can be used in the list, in which case the corresponding names are generated automatically.

`cases h : e`, where `e` is a variable or an expression, performs cases on `e` as above, but also adds a hypothesis `h : e = ...` to each hypothesis, where `...` is the constructor instance for that particular case.
-/
unsafe def cases : parse cases_arg_p → parse with_ident_list → tactic Unit
  | (none, p), ids => do
    let e ← i_to_expr p
    cases_core e ids
  | (some h, p), ids => do
    let x ← get_unused_name
    generalize h () (p, x)
    let hx ← get_local x
    cases_core hx ids

private unsafe def find_matching_hyp (ps : List pattern) : tactic expr :=
  any_hyp fun h => do
    let type ← infer_type h
    ps fun p => do
        match_pattern p type
        return h

/-- `cases_matching p` applies the `cases` tactic to a hypothesis `h : type` if `type` matches the pattern `p`.
`cases_matching [p_1, ..., p_n]` applies the `cases` tactic to a hypothesis `h : type` if `type` matches one of the given patterns.
`cases_matching* p` more efficient and compact version of `focus1 { repeat { cases_matching p } }`. It is more efficient because the pattern is compiled once.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```
cases_matching* [_ ∨ _, _ ∧ _]
```
-/
unsafe def cases_matching (rec : parse <| (tk "*")?) (ps : parse pexpr_list_or_texpr) : tactic Unit := do
  let ps ← ps.mmap pexpr_to_pattern
  if rec then find_matching_hyp ps >>= cases_core
    else tactic.focus1 <| tactic.repeat <| find_matching_hyp ps >>= cases_core

/-- Shorthand for `cases_matching` -/
unsafe def casesm (rec : parse <| (tk "*")?) (ps : parse pexpr_list_or_texpr) : tactic Unit :=
  cases_matching rec ps

private unsafe def try_cases_for_types (type_names : List Name) (at_most_one : Bool) : tactic Unit :=
  any_hyp fun h => do
    let I ← expr.get_app_fn <$> (infer_type h >>= head_beta)
    guardₓ I
    guardₓ (I ∈ type_names)
    tactic.focus1
        (cases_core h >>
          if at_most_one then do
            let n ← num_goals
            guardₓ (n ≤ 1)
          else skip)

/-- `cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
`cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis `h : (I_1 ...)` or ... or `h : (I_n ...)`
`cases_type* I` is shorthand for `focus1 { repeat { cases_type I } }`
`cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```
cases_type* or and
```
-/
unsafe def cases_type (one : parse <| (tk "!")?) (rec : parse <| (tk "*")?) (type_names : parse ident*) : tactic Unit :=
  do
  let type_names ← type_names.mmap resolve_constant
  if rec then try_cases_for_types type_names (bnot one)
    else tactic.focus1 <| tactic.repeat <| try_cases_for_types type_names (bnot one)

/--
Tries to solve the current goal using a canonical proof of `true`, or the `reflexivity` tactic, or the `contradiction` tactic.
-/
unsafe def trivial : tactic Unit :=
  tactic.triv <|> tactic.reflexivity <|> tactic.contradiction <|> fail "trivial tactic failed"

/-- Closes the main goal using `sorry`. Takes an optional ignored tactic block.

The ignored tactic block is useful for "commenting out" part of a proof during development:
```lean
begin
  split,
  admit { expensive_tactic },

end
```
-/
unsafe def admit (t : parse (with_desc "{...}" parser.itactic)?) : tactic Unit :=
  tactic.admit

/-- Closes the main goal using `sorry`. Takes an optional ignored tactic block.

The ignored tactic block is useful for "commenting out" part of a proof during development:
```lean
begin
  split,
  sorry { expensive_tactic },

end
```
-/
unsafe def sorry (t : parse (with_desc "{...}" parser.itactic)?) : tactic Unit :=
  tactic.admit

/--
The contradiction tactic attempts to find in the current local context a hypothesis that is equivalent to an empty inductive type (e.g. `false`), a hypothesis of the form `c_1 ... = c_2 ...` where `c_1` and `c_2` are distinct constructors, or two contradictory hypotheses.
-/
unsafe def contradiction : tactic Unit :=
  tactic.contradiction

/-- `iterate { t }` repeatedly applies tactic `t` until `t` fails. `iterate { t }` always succeeds.

`iterate n { t }` applies `t` `n` times.
-/
unsafe def iterate (n : parse small_nat ?) (t : itactic) : tactic Unit :=
  match n with
  | none => tactic.iterate' t
  | some n => iterate_exactly' n t

/-- `repeat { t }` applies `t` to each goal. If the application succeeds,
the tactic is applied recursively to all the generated subgoals until it eventually fails.
The recursion stops in a subgoal when the tactic has failed to make progress.
The tactic `repeat { t }` never fails.
-/
unsafe def repeat : itactic → tactic Unit :=
  tactic.repeat

/-- `try { t }` tries to apply tactic `t`, but succeeds whether or not `t` succeeds.
-/
unsafe def try : itactic → tactic Unit :=
  tactic.try

/-- A do-nothing tactic that always succeeds.
-/
unsafe def skip : tactic Unit :=
  tactic.skip

/-- `solve1 { t }` applies the tactic `t` to the main goal and fails if it is not solved.
-/
unsafe def solve1 : itactic → tactic Unit :=
  tactic.solve1

/--
`abstract id { t }` tries to use tactic `t` to solve the main goal. If it succeeds, it abstracts the goal as an independent definition or theorem with name `id`. If `id` is omitted, a name is generated automatically.
-/
unsafe def abstract (id : parse ident ?) (tac : itactic) : tactic Unit :=
  tactic.abstract tac id

/-- `all_goals { t }` applies the tactic `t` to every goal, and succeeds if each application succeeds.
-/
unsafe def all_goals : itactic → tactic Unit :=
  tactic.all_goals'

/-- `any_goals { t }` applies the tactic `t` to every goal, and succeeds if at least one application succeeds.
-/
unsafe def any_goals : itactic → tactic Unit :=
  tactic.any_goals'

/--
`focus { t }` temporarily hides all goals other than the first, applies `t`, and then restores the other goals. It fails if there are no goals.
-/
unsafe def focus (tac : itactic) : tactic Unit :=
  tactic.focus1 tac

private unsafe def assume_core (n : Name) (ty : pexpr) := do
  let t ← target
  when (Not <| t ∨ t) whnf_target
  let t ← target
  when (Not <| t ∨ t) <| fail "assume tactic failed, Pi/let expression expected"
  let ty ← i_to_expr (pquote.1 (%%ₓty : Sort _))
  unify ty t
  intro_core n >> skip

/--
Assuming the target of the goal is a Pi or a let, `assume h : t` unifies the type of the binder with `t` and introduces it with name `h`, just like `intro h`. If `h` is absent, the tactic uses the name `this`. If `t` is omitted, it will be inferred.

`assume (h₁ : t₁) ... (hₙ : tₙ)` introduces multiple hypotheses. Any of the types may be omitted, but the names must be present.
-/
unsafe def assume : parse (Sum.inl <$> (tk ":" *> texpr) <|> Sum.inr <$> parse_binders tac_rbp) → tactic Unit
  | Sum.inl ty => assume_core `this ty
  | Sum.inr binders => binders.mmap' fun b => assume_core b.local_pp_name b.local_type

/--
`have h : t := p` adds the hypothesis `h : t` to the current goal if `p` a term of type `t`. If `t` is omitted, it will be inferred.

`have h : t` adds the hypothesis `h : t` to the current goal and opens a new subgoal with target `t`. The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh metavariable.

If `h` is omitted, the name `this` is used.
-/
unsafe def have (h : parse ident ?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse <| (tk ":=" *> texpr)?) : tactic Unit :=
  let h := h.getOrElse `this
  (match q₁, q₂ with
    | some e, some p => do
      let t ← i_to_expr (pquote.1 (%%ₓe : Sort _))
      let v ← i_to_expr (pquote.1 (%%ₓp : %%ₓt))
      tactic.assertv h t v
    | none, some p => do
      let p ← i_to_expr p
      tactic.note h none p
    | some e, none => i_to_expr (pquote.1 (%%ₓe : Sort _)) >>= tactic.assert h
    | none, none => do
      let u ← mk_meta_univ
      let e ← mk_meta_var (sort u)
      tactic.assert h e) >>
    skip

/--
`let h : t := p` adds the hypothesis `h : t := p` to the current goal if `p` a term of type `t`. If `t` is omitted, it will be inferred.

`let h : t` adds the hypothesis `h : t := ?M` to the current goal and opens a new subgoal `?M : t`. The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh metavariable.

If `h` is omitted, the name `this` is used.
-/
unsafe def let (h : parse ident ?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse <| (tk ":=" *> texpr)?) : tactic Unit :=
  let h := h.getOrElse `this
  (match q₁, q₂ with
    | some e, some p => do
      let t ← i_to_expr (pquote.1 (%%ₓe : Sort _))
      let v ← i_to_expr (pquote.1 (%%ₓp : %%ₓt))
      tactic.definev h t v
    | none, some p => do
      let p ← i_to_expr p
      tactic.pose h none p
    | some e, none => i_to_expr (pquote.1 (%%ₓe : Sort _)) >>= tactic.define h
    | none, none => do
      let u ← mk_meta_univ
      let e ← mk_meta_var (sort u)
      tactic.define h e) >>
    skip

/--
`suffices h : t` is the same as `have h : t, tactic.swap`. In other words, it adds the hypothesis `h : t` to the current goal and opens a new subgoal with target `t`.
-/
unsafe def suffices (h : parse ident ?) (t : parse (tk ":" *> texpr)?) : tactic Unit :=
  have h t none >> tactic.swap

/-- This tactic displays the current state in the tracing buffer.
-/
unsafe def trace_state : tactic Unit :=
  tactic.trace_state

/-- `trace a` displays `a` in the tracing buffer.
-/
unsafe def trace {α : Type} [has_to_tactic_format α] (a : α) : tactic Unit :=
  tactic.trace a

/--
`existsi e` will instantiate an existential quantifier in the target with `e` and leave the instantiated body as the new target. More generally, it applies to any inductive type with one constructor and at least two arguments, applying the constructor with `e` as the first argument and leaving the remaining arguments as goals.

`existsi [e₁, ..., eₙ]` iteratively does the same for each expression in the list.
-/
unsafe def existsi : parse pexpr_list_or_texpr → tactic Unit
  | [] => return ()
  | p :: ps => (i_to_expr p >>= tactic.existsi) >> existsi ps

/--
This tactic applies to a goal such that its conclusion is an inductive type (say `I`). It tries to apply each constructor of `I` until it succeeds.
-/
unsafe def constructor : tactic Unit :=
  concat_tags tactic.constructor

/-- Similar to `constructor`, but only non-dependent premises are added as new goals.
-/
unsafe def econstructor : tactic Unit :=
  concat_tags tactic.econstructor

/-- Applies the first constructor when the type of the target is an inductive data type with two constructors.
-/
unsafe def left : tactic Unit :=
  concat_tags tactic.left

/-- Applies the second constructor when the type of the target is an inductive data type with two constructors.
-/
unsafe def right : tactic Unit :=
  concat_tags tactic.right

/-- Applies the constructor when the type of the target is an inductive data type with one constructor.
-/
unsafe def split : tactic Unit :=
  concat_tags tactic.split

private unsafe def constructor_matching_aux (ps : List pattern) : tactic Unit := do
  let t ← target
  ps fun p => match_pattern p t
  constructor

unsafe def constructor_matching (rec : parse <| (tk "*")?) (ps : parse pexpr_list_or_texpr) : tactic Unit := do
  let ps ← ps.mmap pexpr_to_pattern
  if rec then constructor_matching_aux ps else tactic.focus1 <| tactic.repeat <| constructor_matching_aux ps

/-- Replaces the target of the main goal by `false`.
-/
unsafe def exfalso : tactic Unit :=
  tactic.exfalso

/--
The `injection` tactic is based on the fact that constructors of inductive data types are injections. That means that if `c` is a constructor of an inductive datatype, and if `(c t₁)` and `(c t₂)` are two terms that are equal then  `t₁` and `t₂` are equal too.

If `q` is a proof of a statement of conclusion `t₁ = t₂`, then injection applies injectivity to derive the equality of all arguments of `t₁` and `t₂` placed in the same positions. For example, from `(a::b) = (c::d)` we derive `a=c` and `b=d`. To use this tactic `t₁` and `t₂` should be constructor applications of the same constructor.

Given `h : a::b = c::d`, the tactic `injection h` adds two new hypothesis with types `a = c` and `b = d` to the main goal. The tactic `injection h with h₁ h₂` uses the names `h₁` and `h₂` to name the new hypotheses.
-/
unsafe def injection (q : parse texpr) (hs : parse with_ident_list) : tactic Unit := do
  let e ← i_to_expr q
  tactic.injection_with e hs
  try assumption

/-- `injections with h₁ ... hₙ` iteratively applies `injection` to hypotheses using the names `h₁ ... hₙ`.
-/
unsafe def injections (hs : parse with_ident_list) : tactic Unit := do
  tactic.injections_with hs
  try assumption

end Interactive

unsafe structure simp_config_ext extends SimpConfig where
  discharger : tactic Unit := failed

section MkSimpSet

open Expr Interactive.Types

unsafe inductive simp_arg_type : Type
  | all_hyps : simp_arg_type
  | except : Name → simp_arg_type
  | expr : pexpr → simp_arg_type
  | symm_expr : pexpr → simp_arg_type
  deriving has_reflect

unsafe instance simp_arg_type_to_tactic_format : has_to_tactic_format simp_arg_type :=
  ⟨fun a =>
    match a with
    | simp_arg_type.all_hyps => pure "*"
    | simp_arg_type.except n => pure f! "-{n}"
    | simp_arg_type.expr e => i_to_expr_no_subgoals e >>= pp
    | simp_arg_type.symm_expr e => (· ++ ·) "←" <$> (i_to_expr_no_subgoals e >>= pp)⟩

unsafe def simp_arg : parser simp_arg_type :=
  tk "*" *> return simp_arg_type.all_hyps <|>
    tk "-" *> simp_arg_type.except <$> ident <|>
      tk "<-" *> simp_arg_type.symm_expr <$> texpr <|> simp_arg_type.expr <$> texpr

unsafe def simp_arg_list : parser (List simp_arg_type) :=
  tk "*" *> return [simp_arg_type.all_hyps] <|> list_of simp_arg <|> return []

private unsafe def resolve_exception_ids (all_hyps : Bool) :
    List Name → List Name → List Name → tactic (List Name × List Name)
  | [], gex, hex => return (gex.reverse, hex.reverse)
  | id :: ids, gex, hex => do
    let p ← resolve_name id
    let e := p.erase_annotations.get_app_fn.erase_annotations
    match e with
      | const n _ => resolve_exception_ids ids (n :: gex) hex
      | local_const n _ _ _ =>
        when (Not all_hyps) (fail <| s! "invalid local exception {id}, '*' was not used") >>
          resolve_exception_ids ids gex (n :: hex)
      | _ => fail <| s! "invalid exception {id}, unknown identifier"

/-- Decode a list of `simp_arg_type` into lists for each type.

  This is a backwards-compatibility version of `decode_simp_arg_list_with_symm`.
  This version fails when an argument of the form `simp_arg_type.symm_expr`
  is included, so that `simp`-like tactics that do not (yet) support backwards rewriting
  should properly report an error but function normally on other inputs.
-/
unsafe def decode_simp_arg_list (hs : List simp_arg_type) : tactic <| List pexpr × List Name × List Name × Bool := do
  let (hs, ex, all) ←
    hs.mfoldl
        (fun (r : List pexpr × List Name × Bool) h => do
          let (es, ex, all) := r
          match h with
            | simp_arg_type.all_hyps => pure (es, ex, tt)
            | simp_arg_type.except id => pure (es, id :: ex, all)
            | simp_arg_type.expr e => pure (e :: es, ex, all)
            | simp_arg_type.symm_expr _ => fail "arguments of the form '←...' are not supported")
        ([], [], false)
  let (gex, hex) ← resolve_exception_ids all ex [] []
  return (hs, gex, hex, all)

/-- Decode a list of `simp_arg_type` into lists for each type.

  This is the newer version of `decode_simp_arg_list`,
  and has a new name for backwards compatibility.
  This version indicates the direction of a `simp` lemma by including a `bool` with the `pexpr`.
-/
unsafe def decode_simp_arg_list_with_symm (hs : List simp_arg_type) :
    tactic <| List (pexpr × Bool) × List Name × List Name × Bool := do
  let (hs, ex, all) :=
    hs.foldl
      (fun r h =>
        match r, h with
        | (es, ex, all), simp_arg_type.all_hyps => (es, ex, true)
        | (es, ex, all), simp_arg_type.except id => (es, id :: ex, all)
        | (es, ex, all), simp_arg_type.expr e => ((e, false) :: es, ex, all)
        | (es, ex, all), simp_arg_type.symm_expr e => ((e, true) :: es, ex, all))
      ([], [], false)
  let (gex, hex) ← resolve_exception_ids all ex [] []
  return (hs, gex, hex, all)

private unsafe def add_simps : simp_lemmas → List (Name × Bool) → tactic simp_lemmas
  | s, [] => return s
  | s, n :: ns => do
    let s' ← s.add_simp n.fst n.snd
    add_simps s' ns

private unsafe def report_invalid_simp_lemma {α : Type} (n : Name) : tactic α :=
  fail f! "invalid simplification lemma '{n}' (use command 'set_option trace.simp_lemmas true' for more details)"

private unsafe def check_no_overload (p : pexpr) : tactic Unit :=
  when p.is_choice_macro <|
    match p with
    | macro _ ps =>
      fail <| to_fmt "ambiguous overload, possible interpretations" ++ format.join (ps.map fun p => (to_fmt p).indent 4)
    | _ => failed

private unsafe def simp_lemmas.resolve_and_add (s : simp_lemmas) (u : List Name) (n : Name) (ref : pexpr)
    (symm : Bool) : tactic (simp_lemmas × List Name) := do
  let p ← resolve_name n
  check_no_overload p
  let-- unpack local refs
  e := p.erase_annotations.get_app_fn.erase_annotations
  match e with
    | const n _ =>
      (do
          guardₓ ¬symm
          has_attribute `congr n
          let s ← s n
          pure (s, u)) <|>
        (do
            let b ← is_valid_simp_lemma_cnst n
            guardₓ b
            save_const_type_info n ref
            let s ← s n symm
            return (s, u)) <|>
          (do
              let eqns ← get_eqn_lemmas_for tt n
              guardₓ (eqns > 0)
              save_const_type_info n ref
              let s ← add_simps s (eqns fun e => (e, ff))
              return (s, u)) <|>
            (do
                let env ← get_env
                guardₓ (env n).isSome
                return (s, n :: u)) <|>
              report_invalid_simp_lemma n
    | _ =>
      (do
          let e ← i_to_expr_no_subgoals p
          let b ← is_valid_simp_lemma e
          guardₓ b
          try (save_type_info e ref)
          let s ← s e symm
          return (s, u)) <|>
        report_invalid_simp_lemma n

private unsafe def simp_lemmas.add_pexpr (s : simp_lemmas) (u : List Name) (p : pexpr) (symm : Bool) :
    tactic (simp_lemmas × List Name) :=
  match p with
  | const c [] => simp_lemmas.resolve_and_add s u c p symm
  | local_const c _ _ _ => simp_lemmas.resolve_and_add s u c p symm
  | _ => do
    let new_e ← i_to_expr_no_subgoals p
    let s ← s.add new_e symm
    return (s, u)

private unsafe def simp_lemmas.append_pexprs :
    simp_lemmas → List Name → List (pexpr × Bool) → tactic (simp_lemmas × List Name)
  | s, u, [] => return (s, u)
  | s, u, l :: ls => do
    let (s, u) ← simp_lemmas.add_pexpr s u l.fst l.snd
    simp_lemmas.append_pexprs s u ls

unsafe def mk_simp_set_core (no_dflt : Bool) (attr_names : List Name) (hs : List simp_arg_type) (at_star : Bool) :
    tactic (Bool × simp_lemmas × List Name) := do
  let (hs, gex, hex, all_hyps) ← decode_simp_arg_list_with_symm hs
  when (all_hyps ∧ at_star ∧ Not hex) <| fail "A tactic of the form `simp [*, -h] at *` is currently not supported"
  let s ← join_user_simp_lemmas no_dflt attr_names
  let-- Erase `h` from the default simp set for calls of the form `simp [←h]`.
  to_erase :=
    hs.foldl
      (fun l h =>
        match h with
        | (const id _, tt) => id :: l
        | (local_const id _ _ _, tt) => id :: l
        | _ => l)
      []
  let s := s.erase to_erase
  let (s, u) ← simp_lemmas.append_pexprs s [] hs
  let s ←
    if Not at_star ∧ all_hyps then do
        let ctx ← collect_ctx_simps
        let ctx := ctx.filter fun h => h.local_uniq_name ∉ hex
        -- remove local exceptions
            s
            ctx
      else return s
  let gex
    ←-- add equational lemmas, if any
          gex.mmap
        fun n => List.cons n <$> get_eqn_lemmas_for true n
  return (all_hyps, simp_lemmas.erase s <| gex, u)

unsafe def mk_simp_set (no_dflt : Bool) (attr_names : List Name) (hs : List simp_arg_type) :
    tactic (simp_lemmas × List Name) :=
  Prod.snd <$> mk_simp_set_core no_dflt attr_names hs false

end MkSimpSet

namespace Interactive

open _Root_.Interactive Interactive.Types Expr

unsafe def simp_core_aux (cfg : SimpConfig) (discharger : tactic Unit) (s : simp_lemmas) (u : List Name)
    (hs : List expr) (tgt : Bool) : tactic name_set := do
  let (to_remove, lmss) ←
    @List.mfoldl tactic _ (List expr × name_set) _
        (fun ⟨hs, lms⟩ h => do
          let h_type ← infer_type h
          (do
                let (new_h_type, pr, new_lms) ← simplify s u h_type cfg `eq discharger
                assert h new_h_type
                (mk_eq_mp pr h >>= tactic.exact) >> return (h :: hs, lms new_lms)) <|>
              return (hs, lms))
        ([], mk_name_set) hs
  let (lms, goal_simplified) ←
    if tgt then (simp_target s u cfg discharger >>= fun ns => return (ns, true)) <|> return (mk_name_set, false)
      else return (mk_name_set, false)
  guardₓ (cfg = ff ∨ to_remove > 0 ∨ goal_simplified) <|> fail "simplify tactic failed to simplify"
  to_remove fun h => try (clear h)
  return (lmss lms)

unsafe def simp_core (cfg : SimpConfig) (discharger : tactic Unit) (no_dflt : Bool) (hs : List simp_arg_type)
    (attr_names : List Name) (locat : Loc) : tactic name_set := do
  let lms ←
    match locat with
      | loc.wildcard => do
        let (all_hyps, s, u) ← mk_simp_set_core no_dflt attr_names hs true
        if all_hyps then tactic.simp_all s u cfg discharger
          else do
            let hyps ← non_dep_prop_hyps
            simp_core_aux cfg discharger s u hyps tt
      | _ => do
        let (s, u) ← mk_simp_set no_dflt attr_names hs
        let ns ← locat.get_locals
        simp_core_aux cfg discharger s u ns locat
  try tactic.triv
  try (tactic.reflexivity reducible)
  return lms

/--
The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses. It has many variants.

`simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.

`simp [h₁ h₂ ... hₙ]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions. If `hᵢ` is preceded by left arrow (`←` or `<-`), the simplification is performed in the reverse direction. If an `hᵢ` is a defined constant `f`, then the equational lemmas associated with `f` are used. This provides a convenient way to unfold `f`.

`simp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and all hypotheses.

`simp *` is a shorthand for `simp [*]`.

`simp only [h₁ h₂ ... hₙ]` is like `simp [h₁ h₂ ... hₙ]` but does not use `[simp]` lemmas

`simp [-id_1, ... -id_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`, but removes the ones named `idᵢ`.

`simp at h₁ h₂ ... hₙ` simplifies the non-dependent hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. The tactic fails if the target or another hypothesis depends on one of them. The token `⊢` or `|-` can be added to the list to include the target.

`simp at *` simplifies all the hypotheses and the target.

`simp * at *` simplifies target and all (non-dependent propositional) hypotheses using the other hypotheses.

`simp with attr₁ ... attrₙ` simplifies the main goal target using the lemmas tagged with any of the attributes `[attr₁]`, ..., `[attrₙ]` or `[simp]`.
-/
unsafe def simp (use_iota_eqn : parse <| (tk "!")?) (trace_lemmas : parse <| (tk "?")?) (no_dflt : parse only_flag)
    (hs : parse simp_arg_list) (attr_names : parse with_ident_list) (locat : parse location)
    (cfg : simp_config_ext := {  }) : tactic Unit :=
  let cfg :=
    match use_iota_eqn, trace_lemmas with
    | none, none => cfg
    | some _, none => { cfg with iotaEqn := true }
    | none, some _ => { cfg with traceLemmas := true }
    | some _, some _ => { cfg with iotaEqn := true, traceLemmas := true }
  propagate_tags <| do
    let lms ← simp_core cfg.toSimpConfig cfg.discharger no_dflt hs attr_names locat
    if cfg then trace (↑"Try this: simp only " ++ to_fmt lms) else skip

/-- Just construct the simp set and trace it. Used for debugging.
-/
unsafe def trace_simp_set (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list) :
    tactic Unit := do
  let (s, _) ← mk_simp_set no_dflt attr_names hs
  s >>= trace

/--
`simp_intros h₁ h₂ ... hₙ` is similar to `intros h₁ h₂ ... hₙ` except that each hypothesis is simplified as it is introduced, and each introduced hypothesis is used to simplify later ones and the final target.

As with `simp`, a list of simplification lemmas can be provided. The modifiers `only` and `with` behave as with `simp`.
-/
unsafe def simp_intros (ids : parse ident_*) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
    (attr_names : parse with_ident_list) (cfg : SimpIntrosConfig := {  }) : tactic Unit := do
  let (s, u) ← mk_simp_set no_dflt attr_names hs
  when (¬u) (fail s! "simp_intros tactic does not support {u}")
  tactic.simp_intros s u ids cfg
  try triv >> try (reflexivity reducible)

private unsafe def to_simp_arg_list (symms : List Bool) (es : List pexpr) : List simp_arg_type :=
  (symms.zip es).map fun ⟨s, e⟩ => if s then simp_arg_type.symm_expr e else simp_arg_type.expr e

/-- `dsimp` is similar to `simp`, except that it only uses definitional equalities.
-/
unsafe def dsimp (no_dflt : parse only_flag) (es : parse simp_arg_list) (attr_names : parse with_ident_list)
    (l : parse location) (cfg : DsimpConfig := {  }) : tactic Unit := do
  let (s, u) ← mk_simp_set no_dflt attr_names es
  match l with
    | loc.wildcard =>/- Remark: we cannot revert frozen local instances.
         We disable zeta expansion because to prevent `intron n` from failing.
         Another option is to put a "marker" at the current target, and
         implement `intro_upto_marker`. -/
    do
      let n ← revert_all
      dsimp_target s u { cfg with zeta := ff }
      intron n
    | _ => l (fun h => dsimp_hyp h s u cfg) (dsimp_target s u cfg)

/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a reflexive relation, that is, a relation which has a reflexivity lemma tagged with the attribute `[refl]`. The tactic checks whether `t` and `u` are definitionally equal and then solves the goal.
-/
unsafe def reflexivity : tactic Unit :=
  tactic.reflexivity

/-- Shorter name for the tactic `reflexivity`.
-/
unsafe def refl : tactic Unit :=
  tactic.reflexivity

/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation, that is, a relation which has a symmetry lemma tagged with the attribute `[symm]`. It replaces the target with `u ~ t`.
-/
unsafe def symmetry : tactic Unit :=
  tactic.symmetry

/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation, that is, a relation which has a transitivity lemma tagged with the attribute `[trans]`.

`transitivity s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`. If `s` is omitted, then a metavariable is used instead.
-/
unsafe def transitivity (q : parse texpr ?) : tactic Unit :=
  tactic.transitivity >>
    match q with
    | none => skip
    | some q => do
      let (r, lhs, rhs) ← target_lhs_rhs
      i_to_expr q >>= unify rhs

/--
Proves a goal with target `s = t` when `s` and `t` are equal up to the associativity and commutativity of their binary operations.
-/
unsafe def ac_reflexivity : tactic Unit :=
  tactic.ac_refl

/-- An abbreviation for `ac_reflexivity`.
-/
unsafe def ac_refl : tactic Unit :=
  tactic.ac_refl

/-- Tries to prove the main goal using congruence closure.
-/
unsafe def cc : tactic Unit :=
  tactic.cc

/--
Given hypothesis `h : x = t` or `h : t = x`, where `x` is a local constant, `subst h` substitutes `x` by `t` everywhere in the main goal and then clears `h`.
-/
unsafe def subst (q : parse texpr) : tactic Unit :=
  (i_to_expr q >>= tactic.subst) >> try (tactic.reflexivity reducible)

/-- Apply `subst` to all hypotheses of the form `h : x = t` or `h : t = x`.
-/
unsafe def subst_vars : tactic Unit :=
  tactic.subst_vars

/-- `clear h₁ ... hₙ` tries to clear each hypothesis `hᵢ` from the local context.
-/
unsafe def clear : parse ident* → tactic Unit :=
  tactic.clear_lst

private unsafe def to_qualified_name_core : Name → List Name → tactic Name
  | n, [] => fail <| "unknown declaration '" ++ toString n ++ "'"
  | n, ns :: nss => do
    let curr ← return <| ns ++ n
    let env ← get_env
    if env curr then return curr else to_qualified_name_core n nss

private unsafe def to_qualified_name (n : Name) : tactic Name := do
  let env ← get_env
  if env n then return n
    else do
      let ns ← open_namespaces
      to_qualified_name_core n ns

private unsafe def to_qualified_names : List Name → tactic (List Name)
  | [] => return []
  | c :: cs => do
    let new_c ← to_qualified_name c
    let new_cs ← to_qualified_names cs
    return (new_c :: new_cs)

/-- Similar to `unfold`, but only uses definitional equalities.
-/
unsafe def dunfold (cs : parse ident*) (l : parse location) (cfg : DunfoldConfig := {  }) : tactic Unit :=
  match l with
  | loc.wildcard => do
    let ls ← tactic.local_context
    let n ← revert_lst ls
    let new_cs ← to_qualified_names cs
    dunfold_target new_cs cfg
    intron n
  | _ => do
    let new_cs ← to_qualified_names cs
    l (fun h => dunfold_hyp cs h cfg) (dunfold_target new_cs cfg)

private unsafe def delta_hyps : List Name → List Name → tactic Unit
  | cs, [] => skip
  | cs, h :: hs => (get_local h >>= delta_hyp cs) >> delta_hyps cs hs

/--
Similar to `dunfold`, but performs a raw delta reduction, rather than using an equation associated with the defined constants.
-/
unsafe def delta : parse ident* → parse location → tactic Unit
  | cs, loc.wildcard => do
    let ls ← tactic.local_context
    let n ← revert_lst ls
    let new_cs ← to_qualified_names cs
    delta_target new_cs
    intron n
  | cs, l => do
    let new_cs ← to_qualified_names cs
    l (delta_hyp new_cs) (delta_target new_cs)

private unsafe def unfold_projs_hyps (cfg : UnfoldProjConfig := {  }) (hs : List Name) : tactic Bool :=
  hs.mfoldl
    (fun r h => do
      let h ← get_local h
      unfold_projs_hyp h cfg >> return tt <|> return r)
    false

/-- This tactic unfolds all structure projections.
-/
unsafe def unfold_projs (l : parse location) (cfg : UnfoldProjConfig := {  }) : tactic Unit :=
  match l with
  | loc.wildcard => do
    let ls ← local_context
    let b₁ ← unfold_projs_hyps cfg (ls.map expr.local_pp_name)
    let b₂ ← tactic.unfold_projs_target cfg >> return true <|> return false
    when (Not b₁ ∧ Not b₂) (fail "unfold_projs failed to simplify")
  | _ =>
    l.try_apply (fun h => unfold_projs_hyp h cfg) (tactic.unfold_projs_target cfg) <|>
      fail "unfold_projs failed to simplify"

end Interactive

unsafe def ids_to_simp_arg_list (tac_name : Name) (cs : List Name) : tactic (List simp_arg_type) :=
  cs.mmap fun c => do
    let n ← resolve_name c
    let hs ← get_eqn_lemmas_for false n.const_name
    let env ← get_env
    let p := env.is_projection n.const_name
    when (hs ∧ p) (fail s! "{tac_name } tactic failed, {c} does not have equational lemmas nor is a projection")
    return <| simp_arg_type.expr (expr.const c [])

structure UnfoldConfig extends SimpConfig where
  zeta := false
  proj := false
  eta := false
  canonizeInstances := false
  constructorEq := false

namespace Interactive

open _Root_.Interactive Interactive.Types Expr

/--
Given defined constants `e₁ ... eₙ`, `unfold e₁ ... eₙ` iteratively unfolds all occurrences in the target of the main goal, using equational lemmas associated with the definitions.

As with `simp`, the `at` modifier can be used to specify locations for the unfolding.
-/
unsafe def unfold (cs : parse ident*) (locat : parse location) (cfg : UnfoldConfig := {  }) : tactic Unit := do
  let es ← ids_to_simp_arg_list "unfold" cs
  let no_dflt := true
  simp_core cfg failed no_dflt es [] locat
  skip

/-- Similar to `unfold`, but does not iterate the unfolding.
-/
unsafe def unfold1 (cs : parse ident*) (locat : parse location) (cfg : UnfoldConfig := { singlePass := true }) :
    tactic Unit :=
  unfold cs locat cfg

/-- If the target of the main goal is an `opt_param`, assigns the default value.
-/
unsafe def apply_opt_param : tactic Unit :=
  tactic.apply_opt_param

/-- If the target of the main goal is an `auto_param`, executes the associated tactic.
-/
unsafe def apply_auto_param : tactic Unit :=
  tactic.apply_auto_param

/-- Fails if the given tactic succeeds.
-/
unsafe def fail_if_success (tac : itactic) : tactic Unit :=
  tactic.fail_if_success tac

/-- Succeeds if the given tactic fails.
-/
unsafe def success_if_fail (tac : itactic) : tactic Unit :=
  tactic.success_if_fail tac

unsafe def guard_expr_eq (t : expr) (p : parse <| tk ":=" *> texpr) : tactic Unit := do
  let e ← to_expr p
  guardₓ (alpha_eqv t e)

/-- `guard_target t` fails if the target of the main goal is not `t`.
We use this tactic for writing tests.
-/
unsafe def guard_target (p : parse texpr) : tactic Unit := do
  let t ← target
  guard_expr_eq t p

/-- `guard_hyp h : t` fails if the hypothesis `h` does not have type `t`.
We use this tactic for writing tests.
-/
unsafe def guard_hyp (n : parse ident) (ty : parse (tk ":" *> texpr)?) (val : parse (tk ":=" *> texpr)?) :
    tactic Unit := do
  let h ← get_local n
  let ldecl ←
    tactic.unsafe.type_context.run do
        let lctx ← unsafe.type_context.get_local_context
        pure <| lctx h
  let ldecl ← ldecl | fail f! "hypothesis {h} not found"
  match ty with
    | some p => guard_expr_eq ldecl p
    | none => skip
  match ldecl, val with
    | none, some _ => fail f! "{h} is not a let binding"
    | some _, none => fail f! "{h} is a let binding"
    | some hval, some val => guard_expr_eq hval val
    | none, none => skip

/-- `match_target t` fails if target does not match pattern `t`.
-/
unsafe def match_target (t : parse texpr) (m := reducible) : tactic Unit :=
  tactic.match_target t m >> skip

/-- `by_cases p` splits the main goal into two cases, assuming `h : p` in the first branch, and
`h : ¬ p` in the second branch. You can specify the name of the new hypothesis using the syntax
`by_cases h : p`.
-/
unsafe def by_cases : parse cases_arg_p → tactic Unit
  | (n, q) =>
    concat_tags <| do
      let p ← tactic.to_expr_strict q
      tactic.by_cases p (n `h)
      let pos_g :: neg_g :: rest ← get_goals
      return [(`pos, pos_g), (`neg, neg_g)]

/-- Apply function extensionality and introduce new hypotheses.
The tactic `funext` will keep applying new the `funext` lemma until the goal target is not reducible to
```
  |-  ((fun x, ...) = (fun x, ...))
```
The variant `funext h₁ ... hₙ` applies `funext` `n` times, and uses the given identifiers to name the new hypotheses.
-/
unsafe def funext : parse ident_* → tactic Unit
  | [] => tactic.funext >> skip
  | hs => funext_lst hs >> skip

/--
If the target of the main goal is a proposition `p`, `by_contradiction` reduces the goal to proving `false` using the additional hypothesis `h : ¬ p`. `by_contradiction h` can be used to name the hypothesis `h : ¬ p`.

This tactic will attempt to use decidability of `p` if available, and will otherwise fall back on classical reasoning.
-/
unsafe def by_contradiction (n : parse ident ?) : tactic Unit :=
  tactic.by_contradiction (n.getOrElse `h) $> ()

/--
If the target of the main goal is a proposition `p`, `by_contra` reduces the goal to proving `false` using the additional hypothesis `h : ¬ p`. `by_contra h` can be used to name the hypothesis `h : ¬ p`.

This tactic will attempt to use decidability of `p` if available, and will otherwise fall back on classical reasoning.
-/
unsafe def by_contra (n : parse ident ?) : tactic Unit :=
  by_contradiction n

/-- Type check the given expression, and trace its type.
-/
unsafe def type_check (p : parse texpr) : tactic Unit := do
  let e ← to_expr p
  tactic.type_check e
  infer_type e >>= trace

/-- Fail if there are unsolved goals.
-/
unsafe def done : tactic Unit :=
  tactic.done

private unsafe def show_aux (p : pexpr) : List expr → List expr → tactic Unit
  | [], r => fail "show tactic failed"
  | g :: gs, r => do
    (do
          set_goals [g]
          let g_ty ← target
          let ty ← i_to_expr p
          unify g_ty ty
          set_goals (g :: r ++ gs)
          tactic.change ty) <|>
        show_aux gs (g :: r)

/--
`show t` finds the first goal whose target unifies with `t`. It makes that the main goal, performs the unification, and replaces the target with the unified version of `t`.
-/
unsafe def show (q : parse texpr) : tactic Unit := do
  let gs ← get_goals
  show_aux q gs []

/--
The tactic `specialize h a₁ ... aₙ` works on local hypothesis `h`. The premises of this hypothesis, either universal quantifications or non-dependent implications, are instantiated by concrete terms coming either from arguments `a₁` ... `aₙ`. The tactic adds a new hypothesis with the same name `h := h a₁ ... aₙ` and tries to clear the previous one.
-/
unsafe def specialize (p : parse texpr) : tactic Unit :=
  focus1 <| do
    let e ← i_to_expr p
    let h := expr.get_app_fn e
    if h then (tactic.note h none e >> try (tactic.clear h)) >> rotate 1
      else tactic.fail "specialize requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"

unsafe def congr :=
  tactic.congr

end Interactive

end Tactic

section AddInteractive

open Tactic

-- See add_interactive
private unsafe def add_interactive_aux (new_namespace : Name) : List Name → Tactic Unit
  | [] => return ()
  | n :: ns => do
    let env ← get_env
    let d_name ← resolve_constant n
    let declaration.defn _ ls ty val hints trusted ← env.get d_name
    let Name.mk_string h _ ← return d_name
    let new_name := mkStrName new_namespace h
    add_decl (declaration.defn new_name ls ty (expr.const d_name (ls level.param)) hints trusted)
    (do
          let doc ← doc_string d_name
          add_doc_string new_name doc) <|>
        skip
    add_interactive_aux ns

/-- Copy a list of meta definitions in the current namespace to tactic.interactive.

This command is useful when we want to update tactic.interactive without closing the current namespace.
-/
unsafe def add_interactive (ns : List Name) (p : Name := `tactic.interactive) : Tactic Unit :=
  add_interactive_aux p ns

unsafe def has_dup : tactic Bool := do
  let ctx ← local_context
  let p : name_set × Bool :=
    ctx.foldl
      (fun ⟨s, r⟩ h =>
        if r then (s, r) else if s.contains h.local_pp_name then (s, true) else (s.insert h.local_pp_name, false))
      (mk_name_set, false)
  return p.2

/-- Renames hypotheses with the same name.
-/
unsafe def dedup : tactic Unit :=
  mwhen has_dup <| do
    let ctx ← local_context
    let n ← revert_lst ctx
    intron n

end AddInteractive

namespace Tactic

-- Helper tactic for `mk_inj_eq
protected unsafe def apply_inj_lemma : tactic Unit := do
  let h ← intro `h
  let some (lhs, rhs) ← expr.is_eq <$> infer_type h
  let expr.const C _ ← return lhs.get_app_fn
  -- We disable auto_param and opt_param support to address issue #1943
      applyc
      (Name.mk_string "inj" C) { AutoParam := ff, optParam := ff }
  assumption

-- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs]
/- Auxiliary tactic for proving `I.C.inj_eq` lemmas.
   These lemmas are automatically generated by the equation compiler.
   Example:
   ```
   list.cons.inj_eq : forall h1 h2 t1 t2, (h1::t1 = h2::t2) = (h1 = h2 ∧ t1 = t2) :=
   by mk_inj_eq
   ```
-/
unsafe def mk_inj_eq : tactic Unit :=
  sorry

/-
     We use `_root_.*` in the following tactics because
     names are resolved at tactic execution time in interactive mode.
     See PR #1913

     TODO(Leo): This is probably not the only instance of this problem.
     `[ ... ] blocks are convenient to use because they allow us to use the interactive
     mode to write non interactive tactics.
     One potential fix for this issue is to resolve names in `[ ... ] at tactic
     compilation time.
     After this issue is fixed, we should remove the `_root_.*` workaround.
  -/
end Tactic

-- Define inj_eq lemmas for inductive datatypes that were declared before `mk_inj_eq`
universe u v

theorem Sum.inl.inj_eq {α : Type u} (β : Type v) (a₁ a₂ : α) : (@Sum.inl α β a₁ = Sum.inl a₂) = (a₁ = a₂) := by
  run_tac
    tactic.mk_inj_eq

theorem Sum.inr.inj_eq (α : Type u) {β : Type v} (b₁ b₂ : β) : (@Sum.inr α β b₁ = Sum.inr b₂) = (b₁ = b₂) := by
  run_tac
    tactic.mk_inj_eq

theorem PSum.inl.inj_eq {α : Sort u} (β : Sort v) (a₁ a₂ : α) : (@PSum.inl α β a₁ = PSum.inl a₂) = (a₁ = a₂) := by
  run_tac
    tactic.mk_inj_eq

theorem PSum.inr.inj_eq (α : Sort u) {β : Sort v} (b₁ b₂ : β) : (@PSum.inr α β b₁ = PSum.inr b₂) = (b₁ = b₂) := by
  run_tac
    tactic.mk_inj_eq

theorem Sigma.mk.inj_eq {α : Type u} {β : α → Type v} (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) :
    (Sigma.mk a₁ b₁ = Sigma.mk a₂ b₂) = (a₁ = a₂ ∧ HEq b₁ b₂) := by
  run_tac
    tactic.mk_inj_eq

theorem PSigma.mk.inj_eq {α : Sort u} {β : α → Sort v} (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂) :
    (PSigma.mk a₁ b₁ = PSigma.mk a₂ b₂) = (a₁ = a₂ ∧ HEq b₁ b₂) := by
  run_tac
    tactic.mk_inj_eq

theorem Subtype.mk.inj_eq {α : Sort u} {p : α → Prop} (a₁ : α) (h₁ : p a₁) (a₂ : α) (h₂ : p a₂) :
    (Subtype.mk a₁ h₁ = Subtype.mk a₂ h₂) = (a₁ = a₂) := by
  run_tac
    tactic.mk_inj_eq

theorem Option.some.inj_eq {α : Type u} (a₁ a₂ : α) : (some a₁ = some a₂) = (a₁ = a₂) := by
  run_tac
    tactic.mk_inj_eq

theorem List.cons.inj_eq {α : Type u} (h₁ : α) (t₁ : List α) (h₂ : α) (t₂ : List α) :
    (List.cons h₁ t₁ = List.cons h₂ t₂) = (h₁ = h₂ ∧ t₁ = t₂) := by
  run_tac
    tactic.mk_inj_eq

theorem Nat.succ.inj_eq (n₁ n₂ : Nat) : (Nat.succ n₁ = Nat.succ n₂) = (n₁ = n₂) := by
  run_tac
    tactic.mk_inj_eq

