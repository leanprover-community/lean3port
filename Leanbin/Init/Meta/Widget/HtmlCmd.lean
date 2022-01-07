prelude
import Leanbin.Init.Meta.Widget.Basic
import Leanbin.Init.Meta.Lean.Parser
import Leanbin.Init.Meta.InteractiveBase
import Leanbin.Init.Data.Punit

open Lean

open Lean.Parser

open Interactive

open Tactic

open Widget

/-- Accepts terms with the type `component tactic_state empty` or `html empty` and
renders them interactively. -/
@[user_command]
unsafe def show_widget_cmd (x : parse $ tk "#html") : parser Unit := do
  let ⟨l, c⟩ ← cur_pos
  let y ← parser.pexpr 0
  let comp ←
    parser.of_tactic
        ((do
            tactic.eval_pexpr (component tactic_state Empty) y) <|>
          do
          let htm : html Empty ← tactic.eval_pexpr (html Empty) y
          let c : component Unit Empty ← pure $ component.stateless fun _ => [htm]
          pure $ component.ignore_props $ component.ignore_action $ c)
  save_widget ⟨l, c - "#html".length - 1⟩ comp
  trace "successfully rendered widget" pure ()

run_cmd
  skip

