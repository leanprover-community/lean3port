/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Control.Monad
import Leanbin.Init.Meta.Format
import Leanbin.Init.Util

/-- An exceptional is similar to `Result` in Haskell.-/
/-
Remark: we use a function that produces a format object as the exception information.
Motivation: the formatting object may be big, and we may create it on demand.
-/
/-
Remark: we use a function that produces a format object as the exception information.
Motivation: the formatting object may be big, and we may create it on demand.
-/
unsafe inductive exceptional (α : Type)
  | success : α → exceptional
  | exception : (options → format) → exceptional

section

open Exceptional

variable {α : Type}

variable [HasToString α]

protected unsafe def exceptional.to_string : exceptional α → Stringₓ
  | success a => toString a
  | exception e => "Exception: " ++ toString (e options.mk)

unsafe instance : HasToString (exceptional α) :=
  HasToString.mk exceptional.to_string

end

namespace Exceptional

variable {α β : Type}

protected unsafe def to_bool : exceptional α → Bool
  | success _ => true
  | exception _ => false

protected unsafe def to_option : exceptional α → Option α
  | success a => some a
  | exception _ => none

@[inline]
protected unsafe def bind (e₁ : exceptional α) (e₂ : α → exceptional β) : exceptional β :=
  exceptional.cases_on e₁ (fun a => e₂ a) fun f => exception f

@[inline]
protected unsafe def return (a : α) : exceptional α :=
  success a

@[inline]
unsafe def fail (f : format) : exceptional α :=
  exception fun u => f

end Exceptional

unsafe instance : Monadₓ exceptional where
  pure := @exceptional.return
  bind := @exceptional.bind

