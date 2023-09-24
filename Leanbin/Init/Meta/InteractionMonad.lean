/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Function
import Init.Data.Option.Basic
import Init.Util
import Init.Control.Combinators
import Init.Control.Monad
import Init.Control.Alternative
import Init.Control.MonadFail
import Init.Data.Nat.Div
import Init.Meta.Exceptional
import Init.Meta.Format
import Init.Meta.Environment
import Init.Meta.Pexpr
import Init.Data.Repr
import Init.Data.String.Basic
import Init.Data.ToString

#align_import init.meta.interaction_monad from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

universe u v

unsafe inductive interaction_monad.result (state : Type) (α : Type u)
  | success : α → StateM → interaction_monad.result
  | exception : Option (Unit → format) → Option Pos → StateM → interaction_monad.result
#align interaction_monad.result interaction_monad.result

open InteractionMonad.Result

section

variable {state : Type} {α : Type u}

variable [ToString α]

unsafe def interaction_monad.result_to_string : result StateM α → String
  | success a s => toString a
  | exception (some t) ref s => "Exception: " ++ toString (t ())
  | exception none ref s => "[silent exception]"
#align interaction_monad.result_to_string interaction_monad.result_to_string

unsafe instance interaction_monad.result_has_string : ToString (result StateM α) :=
  ⟨interaction_monad.result_to_string⟩
#align interaction_monad.result_has_string interaction_monad.result_has_string

end

unsafe def interaction_monad.result.clamp_pos {state : Type} {α : Type u} (line0 line col : ℕ) :
    result StateM α → result StateM α
  | success a s => success a s
  | exception msg (some p) s => exception msg (some <| if p.line < line0 then ⟨line, col⟩ else p) s
  | exception msg none s => exception msg (some ⟨line, col⟩) s
#align interaction_monad.result.clamp_pos interaction_monad.result.clamp_pos

@[reducible]
unsafe def interaction_monad (state : Type) (α : Type u) :=
  StateM → result StateM α
#align interaction_monad interaction_monad

section

parameter {state : Type}

variable {α : Type u} {β : Type v}

local notation "m" => interaction_monad StateM

@[inline]
unsafe def interaction_monad_fmap (f : α → β) (t : m α) : m β := fun s =>
  interaction_monad.result.cases_on (t s) (fun a s' => success (f a) s') fun e s' => exception e s'
#align interaction_monad_fmap interaction_monad_fmap

@[inline]
unsafe def interaction_monad_bind (t₁ : m α) (t₂ : α → m β) : m β := fun s =>
  interaction_monad.result.cases_on (t₁ s) (fun a s' => t₂ a s') fun e s' => exception e s'
#align interaction_monad_bind interaction_monad_bind

@[inline]
unsafe def interaction_monad_return (a : α) : m α := fun s => success a s
#align interaction_monad_return interaction_monad_return

unsafe def interaction_monad_orelse {α : Type u} (t₁ t₂ : m α) : m α := fun s =>
  interaction_monad.result.cases_on (t₁ s) success fun e₁ ref₁ s' =>
    interaction_monad.result.cases_on (t₂ s) success exception
#align interaction_monad_orelse interaction_monad_orelse

@[inline]
unsafe def interaction_monad_seq (t₁ : m α) (t₂ : m β) : m β :=
  interaction_monad_bind t₁ fun a => t₂
#align interaction_monad_seq interaction_monad_seq

unsafe instance interaction_monad.monad : Monad m
    where
  map := @interaction_monad_fmap
  pure := @interaction_monad_return
  bind := @interaction_monad_bind
#align interaction_monad.monad interaction_monad.monad

unsafe def interaction_monad.mk_exception {α : Type u} {β : Type v} [has_to_format β] (msg : β)
    (ref : Option expr) (s : StateM) : result StateM α :=
  exception (some fun _ => to_fmt msg) none s
#align interaction_monad.mk_exception interaction_monad.mk_exception

unsafe def interaction_monad.fail {α : Type u} {β : Type v} [has_to_format β] (msg : β) : m α :=
  fun s => interaction_monad.mk_exception msg none s
#align interaction_monad.fail interaction_monad.fail

unsafe def interaction_monad.silent_fail {α : Type u} : m α := fun s => exception none none s
#align interaction_monad.silent_fail interaction_monad.silent_fail

unsafe def interaction_monad.failed {α : Type u} : m α :=
  interaction_monad.fail "failed"
#align interaction_monad.failed interaction_monad.failed

/-- Alternative orelse operator that allows to select which exception should be used.
   The default is to use the first exception since the standard `orelse` uses the second. -/
unsafe def interaction_monad.orelse' {α : Type u} (t₁ t₂ : m α) (use_first_ex := true) : m α :=
  fun s =>
  interaction_monad.result.cases_on (t₁ s) success fun e₁ ref₁ s₁' =>
    interaction_monad.result.cases_on (t₂ s) success fun e₂ ref₂ s₂' =>
      if use_first_ex then exception e₁ ref₁ s₁' else exception e₂ ref₂ s₂'
#align interaction_monad.orelse' interaction_monad.orelse'

unsafe instance interaction_monad.monad_fail : MonadFail m :=
  { interaction_monad.monad with fail := fun α s => interaction_monad.fail (to_fmt s) }
#align interaction_monad.monad_fail interaction_monad.monad_fail

@[inline]
unsafe def interaction_monad.bracket {α β γ} (x : m α) (inside : m β) (y : m γ) : m β :=
  x >> fun s =>
    match inside s with
    | success r s' => (y >> success r) s'
    | exception msg p s' => (y >> exception msg p) s'
#align interaction_monad.bracket interaction_monad.bracket

-- TODO: unify `parser` and `tactic` behavior?
-- meta instance interaction_monad.alternative : alternative m :=
-- ⟨@interaction_monad_fmap, (λ α a s, success a s), (@fapp _ _), @interaction_monad.failed, @interaction_monad_orelse⟩
end

