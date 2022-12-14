/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.exceptional
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Control.Monad
import Leanbin.Init.Meta.Format
import Leanbin.Init.Util

/-- An exceptional is similar to `Result` in Haskell.

Remark: we use a function that produces a format object as the exception information.
Motivation: the formatting object may be big, and we may create it on demand.-/
unsafe inductive exceptional (α : Type)
  | success : α → exceptional
  | exception : (options → format) → exceptional
#align exceptional exceptional

section

open Exceptional

variable {α : Type}

variable [ToString α]

protected unsafe def exceptional.to_string : exceptional α → String
  | success a => toString a
  | exception e => "Exception: " ++ toString (e options.mk)
#align exceptional.to_string exceptional.to_string

unsafe instance : ToString (exceptional α) :=
  ToString.mk exceptional.to_string

end

namespace Exceptional

variable {α β : Type}

protected unsafe def to_bool : exceptional α → Bool
  | success _ => true
  | exception _ => false
#align exceptional.to_bool exceptional.to_bool

protected unsafe def to_option : exceptional α → Option α
  | success a => some a
  | exception _ => none
#align exceptional.to_option exceptional.to_option

@[inline]
protected unsafe def bind (e₁ : exceptional α) (e₂ : α → exceptional β) : exceptional β :=
  exceptional.cases_on e₁ (fun a => e₂ a) fun f => exception f
#align exceptional.bind exceptional.bind

@[inline]
protected unsafe def return (a : α) : exceptional α :=
  success a
#align exceptional.return exceptional.return

@[inline]
unsafe def fail (f : format) : exceptional α :=
  exception fun u => f
#align exceptional.fail exceptional.fail

end Exceptional

unsafe instance : Monad exceptional where 
  pure := @exceptional.return
  bind := @exceptional.bind

