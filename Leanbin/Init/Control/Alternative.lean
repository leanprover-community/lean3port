/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.control.alternative
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Control.Applicative

universe u v

class HasOrelse (f : Type u → Type v) : Type max (u + 1) v where
  orelse : ∀ {α : Type u}, f α → f α → f α
#align has_orelse HasOrelse

#print Alternative /-
class Alternative (f : Type u → Type v) extends Applicative f, HasOrelse f :
  Type max (u + 1) v where
  failure : ∀ {α : Type u}, f α
#align alternative Alternative
-/

section

variable {f : Type u → Type v} [Alternative f] {α : Type u}

@[inline]
def failure : f α :=
  Alternative.failure
#align failure failure

#print guard /-
/-- If the condition `p` is decided to be false, then fail, otherwise, return unit. -/
@[inline]
def guard {f : Type → Type v} [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then pure () else failure
#align guard guard
-/

@[inline]
def assert {f : Type → Type v} [Alternative f] (p : Prop) [Decidable p] : f (Inhabited p) :=
  if h : p then pure ⟨h⟩ else failure
#align assert assert

/- Later we define a coercion from bool to Prop, but this version will still be useful.
   Given (t : tactic bool), we can write t >>= guardb -/
@[inline]
def guardb {f : Type → Type v} [Alternative f] : Bool → f Unit
  | tt => pure ()
  | ff => failure
#align guardb guardb

#print optional /-
@[inline]
def optional (x : f α) : f (Option α) :=
  some <$> x <|> pure none
#align optional optional
-/

end

