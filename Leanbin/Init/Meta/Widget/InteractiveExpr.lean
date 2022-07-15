/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import Leanbin.Init.Meta.Widget.Basic
import Leanbin.Init.Meta.Widget.TacticComponent
import Leanbin.Init.Meta.TaggedFormat
import Leanbin.Init.Data.Punit
import Leanbin.Init.Meta.MkDecEqInstance

unsafe def subexpr :=
  expr × Expr.Address

namespace Widget

open TaggedFormat

open Html Attr

namespace InteractiveExpression

/-- eformat but without any of the formatting stuff like highlighting, groups etc. -/
unsafe inductive sf : Type
  | tag_expr : Expr.Address → expr → sf → sf
  | compose : sf → sf → sf
  | of_string : Stringₓ → sf

unsafe def sf.repr : sf → format
  | sf.tag_expr addr e a =>
    format.group <|
      format.nest 2 <|
        "(tag_expr " ++ to_fmt addr ++ format.line ++ "`(" ++ to_fmt e ++ ")" ++ format.line ++ a.repr ++ ")"
  | sf.compose a b => a.repr ++ format.line ++ b.repr
  | sf.of_string s => reprₓ s

unsafe instance : has_to_format sf :=
  ⟨sf.repr⟩

unsafe instance : HasToString sf :=
  ⟨fun s => s.repr.toString⟩

unsafe instance : HasRepr sf :=
  ⟨fun s => s.repr.toString⟩

unsafe def sf.of_eformat : eformat → sf
  | tag ⟨ea, e⟩ m => sf.tag_expr ea e <| sf.of_eformat m
  | group m => sf.of_eformat m
  | nest i m => sf.of_eformat m
  | highlight i m => sf.of_eformat m
  | of_format f => sf.of_string <| format.to_string f
  | compose x y => sf.compose (sf.of_eformat x) (sf.of_eformat y)

unsafe def sf.flatten : sf → sf
  | sf.tag_expr e ea m => sf.tag_expr e ea <| sf.flatten m
  | sf.compose x y =>
    match sf.flatten x, sf.flatten y with
    | sf.of_string sx, sf.of_string sy => sf.of_string (sx ++ sy)
    | sf.of_string sx, sf.compose (sf.of_string sy) z => sf.compose (sf.of_string (sx ++ sy)) z
    | sf.compose x (sf.of_string sy), sf.of_string sz => sf.compose x (sf.of_string (sy ++ sz))
    | sf.compose x (sf.of_string sy1), sf.compose (sf.of_string sy2) z =>
      sf.compose x (sf.compose (sf.of_string (sy1 ++ sy2)) z)
    | x, y => sf.compose x y
  | sf.of_string s => sf.of_string s

unsafe inductive action (γ : Type)
  | on_mouse_enter : subexpr → action
  | on_mouse_leave_all : action
  | on_click : subexpr → action
  | on_tooltip_action : γ → action
  | on_close_tooltip : action

unsafe def view {γ} (tooltip_component : tc subexpr (action γ)) (click_address : Option Expr.Address)
    (select_address : Option Expr.Address) : subexpr → sf → tactic (List (html (action γ)))
  | ⟨ce, current_address⟩, sf.tag_expr ea e m => do
    let new_address := current_address ++ ea
    let select_attrs : List (attr (action γ)) :=
      if some new_address = select_address then [className "highlight"] else []
    let click_attrs : List (attr (action γ)) ←
      if some new_address = click_address then do
          let content ← tc.to_html tooltip_component (e, new_address)
          pure
              [tooltip <|
                  h "div" []
                    [h "button" [cn "fr pointer ba br3", on_click fun _ => action.on_close_tooltip] ["x"], content]]
        else pure []
    let as := [className "expr-boundary", key ea] ++ select_attrs ++ click_attrs
    let inner ← view (e, new_address) m
    pure [h "span" as inner]
  | ca, sf.compose x y => pure (· ++ ·) <*> view ca x <*> view ca y
  | ca, sf.of_string s =>
    pure
      [h "span" [on_mouse_enter fun _ => action.on_mouse_enter ca, on_click fun _ => action.on_click ca, key s]
          [html.of_string s]]

/-- Make an interactive expression. -/
unsafe def mk {γ} (tooltip : tc subexpr γ) : tc expr γ :=
  let tooltip_comp :=
    (component.with_should_update fun x y : tactic_state × expr × Expr.Address => x.2.2 ≠ y.2.2) <|
      component.map_action action.on_tooltip_action tooltip
  tc.mk_simple (action γ) (Option subexpr × Option subexpr) (fun e => pure <| (none, none))
    (fun e ⟨ca, sa⟩ act =>
      pure <|
        match act with
        | action.on_mouse_enter ⟨e, ea⟩ => ((ca, some (e, ea)), none)
        | action.on_mouse_leave_all => ((ca, none), none)
        | action.on_click ⟨e, ea⟩ => if some (e, ea) = ca then ((none, sa), none) else ((some (e, ea), sa), none)
        | action.on_tooltip_action g => ((none, sa), some g)
        | action.on_close_tooltip => ((none, sa), none))
    fun e ⟨ca, sa⟩ => do
    let ts ← tactic.read
    let m : sf := sf.flatten <| sf.of_eformat <| tactic_state.pp_tagged ts e
    let m : sf := sf.tag_expr [] e m
    let v
      ←-- [hack] in pp.cpp I forgot to add an expr-boundary for the root expression.
          view
          tooltip_comp (Prod.snd <$> ca) (Prod.snd <$> sa) ⟨e, []⟩ m
    pure <| [h "span" [className "expr", key e, on_mouse_leave fun _ => action.on_mouse_leave_all] <| v]

/-- Render the implicit arguments for an expression in fancy, little pills. -/
unsafe def implicit_arg_list (tooltip : tc subexpr Empty) (e : expr) : tactic <| html Empty := do
  let fn ← mk tooltip <| expr.get_app_fn e
  let args ← List.mmapₓ (mk tooltip) <| expr.get_app_args e
  pure <|
      h "div" []
        (h "span" [className "bg-blue br3 ma1 ph2 white"] [fn] ::
          List.map (fun a => h "span" [className "bg-gray br3 ma1 ph2 white"] [a]) args)

unsafe def type_tooltip : tc subexpr Empty :=
  tc.stateless fun ⟨e, ea⟩ => do
    let y ← tactic.infer_type e
    let y_comp ← mk type_tooltip y
    let implicit_args ← implicit_arg_list type_tooltip e
    pure [h "div" [] [h "div" [] [y_comp], h "hr" [] [], implicit_args]]

end InteractiveExpression

unsafe inductive filter_type
  | none
  | no_instances
  | only_props
  deriving DecidableEq

unsafe def filter_local : filter_type → expr → tactic Bool
  | filter_type.none, e => pure true
  | filter_type.no_instances, e => do
    let t ← tactic.infer_type e
    bnot <$> tactic.is_class t
  | filter_type.only_props, e => do
    let t ← tactic.infer_type e
    tactic.is_prop t

unsafe def filter_component : component filter_type filter_type :=
  component.stateless fun lf =>
    [h "label" [] ["filter: "],
      select
        [⟨filter_type.none, "0", ["no filter"]⟩, ⟨filter_type.no_instances, "1", ["no instances"]⟩,
          ⟨filter_type.only_props, "2", ["only props"]⟩]
        lf]

unsafe def html.of_name {α : Type} : Name → html α
  | n => html.of_string <| Name.toString n

open Tactic

unsafe def show_type_component : tc expr Empty :=
  tc.stateless fun x => do
    let y ← infer_type x
    let y_comp ← interactive_expression.mk interactive_expression.type_tooltip <| y
    pure y_comp

/-- A group of local constants in the context that should be rendered as one line. -/
unsafe structure local_collection where
  key : Stringₓ
  locals : List expr
  type : expr
  deriving DecidableEq

/-- Group consecutive locals according to whether they have the same type -/
unsafe def to_local_collection : List local_collection → List expr → tactic (List local_collection)
  | Acc, [] =>
    pure <| (List.map fun lc : local_collection => { lc with locals := lc.locals.reverse }) <| List.reverse <| Acc
  | Acc, l :: ls => do
    let l_type ← infer_type l
    (do
          let ⟨k, ns, t⟩ :: Acc ← pure Acc
          is_def_eq t l_type
          to_local_collection (⟨k, l :: ns, t⟩ :: Acc) ls) <|>
        to_local_collection (⟨toString <| expr.local_uniq_name <| l, [l], l_type⟩ :: Acc) ls

/-- Component that displays the main (first) goal. -/
unsafe def tactic_view_goal {γ} (local_c : tc local_collection γ) (target_c : tc expr γ) : tc filter_type γ :=
  tc.stateless fun ft => do
    let g@(expr.mvar u_n pp_n y) ← main_goal
    let t ← get_tag g
    let case_tag : List (html γ) :=
      match interactive.case_tag.parse t with
      | some t =>
        [h "li" [key "_case"] <| [h "span" [cn "goal-case b"] ["case"]] ++ t.case_names.bind fun n => [" ", n]]
      | none => []
    let lcs ← local_context
    let lcs ← List.mfilter (filter_local ft) lcs
    let lcs ← to_local_collection [] lcs
    let lchs ←
      lcs.mmap fun lc => do
          let lh ← local_c lc
          let ns ← pure <| lc.locals.map fun n => h "span" [cn "goal-hyp b pr2"] [html.of_name <| expr.local_pp_name n]
          pure <| h "li" [key lc] (ns ++ [": ", h "span" [cn "goal-hyp-type"] [lh]])
    let t_comp ← target_c g
    pure <|
        h "ul" [key g, className "list pl0 font-code"] <|
          case_tag ++ lchs ++ [h "li" [key u_n] [h "span" [cn "goal-vdash b"] ["⊢ "], t_comp]]

unsafe inductive tactic_view_action (γ : Type)
  | out (a : γ) : tactic_view_action
  | filter (f : filter_type) : tactic_view_action

/-- Component that displays all goals, together with the `$n goals` message. -/
unsafe def tactic_view_component {γ} (local_c : tc local_collection γ) (target_c : tc expr γ) : tc Unit γ :=
  tc.mk_simple (tactic_view_action γ) filter_type (fun _ => pure <| filter_type.none)
    (fun ⟨⟩ ft a =>
      match a with
      | tactic_view_action.out a => pure (ft, some a)
      | tactic_view_action.filter ft => pure (ft, none))
    fun ⟨⟩ ft => do
    let gs ← get_goals
    let hs ←
      gs.mmap fun g => do
          set_goals [g]
          flip tc.to_html ft <| tactic_view_goal local_c target_c
    set_goals gs
    let goal_message :=
      if gs.length = 0 then "goals accomplished" else if gs.length = 1 then "1 goal" else toString gs.length ++ " goals"
    let goal_message : html γ := h "strong" [cn "goal-goals"] [goal_message]
    let goals : html γ :=
      h "ul" [className "list pl0"] <|
        (List.mapWithIndex fun i x => h "li" [className <| "lh-copy mt2", key i] [x]) <| goal_message :: hs
    pure
        [h "div" [className "fr"]
            [html.of_component ft <| component.map_action tactic_view_action.filter filter_component],
          html.map_action tactic_view_action.out goals]

/-- Component that displays the term-mode goal. -/
unsafe def tactic_view_term_goal {γ} (local_c : tc local_collection γ) (target_c : tc expr γ) : tc Unit γ :=
  tc.stateless fun _ => do
    let goal ← flip tc.to_html filter_type.none <| tactic_view_goal local_c target_c
    pure
        [h "ul" [className "list pl0"]
            [h "li" [className "lh-copy"] [h "strong" [cn "goal-goals"] ["expected type:"]],
              h "li" [className "lh-copy"] [goal]]]

unsafe def show_local_collection_component : tc local_collection Empty :=
  tc.stateless fun lc => do
    let l :: _ ← pure lc.locals
    let c ← show_type_component l
    pure [c]

unsafe def tactic_render : tc Unit Empty :=
  component.ignore_action <| tactic_view_component show_local_collection_component show_type_component

unsafe def tactic_state_widget : component tactic_state Empty :=
  tc.to_component tactic_render

/-- Widget used to display term-proof goals.
-/
unsafe def term_goal_widget : component tactic_state Empty :=
  (tactic_view_term_goal show_local_collection_component show_type_component).to_component

end Widget

