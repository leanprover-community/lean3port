/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Leanbin.Init.Function
import Leanbin.Init.Data.Option.Basic
import Leanbin.Init.Util
import Leanbin.Init.Control.Combinators
import Leanbin.Init.Control.Monad
import Leanbin.Init.Control.Alternative
import Leanbin.Init.Control.MonadFail
import Leanbin.Init.Data.Nat.Div
import Leanbin.Init.Meta.Exceptional
import Leanbin.Init.Meta.Format
import Leanbin.Init.Meta.Environment
import Leanbin.Init.Meta.Pexpr
import Leanbin.Init.Data.Repr
import Leanbin.Init.Data.String.Basic
import Leanbin.Init.Data.ToString

universe u v

unsafe inductive interaction_monad.result (state : Type) (α : Type u)
  | success : α → state → interaction_monad.result
  | exception : Option (Unit → format) → Option Pos → state → interaction_monad.result

open InteractionMonad.Result

section

variable {state : Type} {α : Type u}

variable [HasToString α]

unsafe def interaction_monad.result_to_string : result state α → Stringₓ
  | success a s => toString a
  | exception (some t) ref s => "Exception: " ++ toString (t ())
  | exception none ref s => "[silent exception]"

unsafe instance interaction_monad.result_has_string : HasToString (result state α) :=
  ⟨interaction_monad.result_to_string⟩

end

unsafe def interaction_monad.result.clamp_pos {state : Type} {α : Type u} (line0 line col : ℕ) :
    result state α → result state α
  | success a s => success a s
  | exception msg (some p) s => exception msg (some <| if p.line < line0 then ⟨line, col⟩ else p) s
  | exception msg none s => exception msg (some ⟨line, col⟩) s

@[reducible]
unsafe def interaction_monad (state : Type) (α : Type u) :=
  state → result state α

section

parameter {state : Type}

variable {α : Type u} {β : Type v}

-- mathport name: «exprm»
local notation "m" => interaction_monad state

@[inline]
unsafe def interaction_monad_fmap (f : α → β) (t : m α) : m β := fun s =>
  interaction_monad.result.cases_on (t s) (fun a s' => success (f a) s') fun e s' => exception e s'

@[inline]
unsafe def interaction_monad_bind (t₁ : m α) (t₂ : α → m β) : m β := fun s =>
  interaction_monad.result.cases_on (t₁ s) (fun a s' => t₂ a s') fun e s' => exception e s'

@[inline]
unsafe def interaction_monad_return (a : α) : m α := fun s => success a s

unsafe def interaction_monad_orelse {α : Type u} (t₁ t₂ : m α) : m α := fun s =>
  interaction_monad.result.cases_on (t₁ s) success fun e₁ ref₁ s' =>
    interaction_monad.result.cases_on (t₂ s) success exception

@[inline]
unsafe def interaction_monad_seq (t₁ : m α) (t₂ : m β) : m β :=
  interaction_monad_bind t₁ fun a => t₂

unsafe instance interaction_monad.monad : Monadₓ m where
  map := @interaction_monad_fmap
  pure := @interaction_monad_return
  bind := @interaction_monad_bind

unsafe def interaction_monad.mk_exception {α : Type u} {β : Type v} [has_to_format β] (msg : β) (ref : Option expr)
    (s : state) : result state α :=
  exception (some fun _ => to_fmt msg) none s

unsafe def interaction_monad.fail {α : Type u} {β : Type v} [has_to_format β] (msg : β) : m α := fun s =>
  interaction_monad.mk_exception msg none s

unsafe def interaction_monad.silent_fail {α : Type u} : m α := fun s => exception none none s

unsafe def interaction_monad.failed {α : Type u} : m α :=
  interaction_monad.fail "failed"

/- Alternative orelse operator that allows to select which exception should be used.
   The default is to use the first exception since the standard `orelse` uses the second. -/
unsafe def interaction_monad.orelse' {α : Type u} (t₁ t₂ : m α) (use_first_ex := true) : m α := fun s =>
  interaction_monad.result.cases_on (t₁ s) success fun e₁ ref₁ s₁' =>
    interaction_monad.result.cases_on (t₂ s) success fun e₂ ref₂ s₂' =>
      if use_first_ex then exception e₁ ref₁ s₁' else exception e₂ ref₂ s₂'

unsafe instance interaction_monad.monad_fail : MonadFail m :=
  { interaction_monad.monad with fail := fun α s => interaction_monad.fail (to_fmt s) }

@[inline]
unsafe def interaction_monad.bracket {α β γ} (x : m α) (inside : m β) (y : m γ) : m β :=
  x >> fun s =>
    match inside s with
    | success r s' => (y >> success r) s'
    | exception msg p s' => (y >> exception msg p) s'

-- TODO: unify `parser` and `tactic` behavior?
-- meta instance interaction_monad.alternative : alternative m :=
-- ⟨@interaction_monad_fmap, (λ α a s, success a s), (@fapp _ _), @interaction_monad.failed, @interaction_monad_orelse⟩
end

