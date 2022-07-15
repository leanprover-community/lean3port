/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import Leanbin.Init.Meta.Widget.Basic

namespace Widget

/--
A component that implicitly depends on tactic_state. For efficiency we always assume that the tactic_state is unchanged between component renderings. -/
unsafe def tc (π : Type) (α : Type) :=
  component (tactic_state × π) α

namespace Tc

variable {π ρ α β : Type}

unsafe def of_component : component π α → tc π α :=
  component.map_props Prod.snd

unsafe def map_action (f : α → β) : tc π α → tc π β :=
  component.map_action f

unsafe def map_props (f : π → ρ) : tc ρ α → tc π α :=
  component.map_props (Prod.map id f)

open InteractionMonad

open InteractionMonad.Result

/-- Make a tactic component from some init, update, views which are expecting a tactic.
The tactic_state never mutates.
-/
unsafe def mk_simple [DecidableEq π] (β σ : Type) (init : π → tactic σ) (update : π → σ → β → tactic (σ × Option α))
    (view : π → σ → tactic (List (html β))) : tc π α :=
  (component.with_should_update fun ⟨_, old_p⟩ ⟨_, new_p⟩ => old_p ≠ new_p) <|
    @component.stateful (tactic_state × π) α β (interaction_monad.result tactic_state σ)
      (fun ⟨ts, p⟩ last =>
        match last with
        | some x => x
        | none => init p ts)
      (fun ⟨ts, p⟩ s b =>
        match s with
        | success s _ =>
          match update p s b ts with
          | success ⟨s, a⟩ _ => Prod.mk (success s ts) a
          | exception m p ts' => Prod.mk (exception m p ts') none
        | x => ⟨x, none⟩)
      fun ⟨ts, p⟩ s =>
      match s with
      | success s _ =>
        match view p s ts with
        | success h _ => h
        | exception msg Pos s => ["rendering tactic failed "]
      | exception msg Pos s => ["state of tactic component has failed!"]

unsafe def stateless [DecidableEq π] (view : π → tactic (List (html α))) : tc π α :=
  tc.mk_simple α Unit (fun p => pure ()) (fun _ _ b => pure ((), some b)) fun p _ => view p

unsafe def to_html : tc π α → π → tactic (html α)
  | c, p, ts => success (html.of_component (ts, p) c) ts

unsafe def to_component : tc Unit α → component tactic_state α
  | c => component.map_props (fun tc => (tc, ())) c

unsafe instance : CoeFun (tc π α) fun x => π → tactic (html α) :=
  ⟨to_html⟩

end Tc

end Widget

