/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Control.Applicative

universe u v

class HasOrelse (f : Type u → Type v) : Type max (u + 1) v where
  orelse : ∀ {α : Type u}, f α → f α → f α

class Alternativeₓ (f : Type u → Type v) extends Applicativeₓ f, HasOrelse f : Type max (u + 1) v where
  failure : ∀ {α : Type u}, f α

section

variable {f : Type u → Type v} [Alternativeₓ f] {α : Type u}

@[inline]
def failure : f α :=
  Alternativeₓ.failure

/-- If the condition `p` is decided to be false, then fail, otherwise, return unit. -/
@[inline]
def guardₓ {f : Type → Type v} [Alternativeₓ f] (p : Prop) [Decidable p] : f Unit :=
  if p then pure () else failure

@[inline]
def assert {f : Type → Type v} [Alternativeₓ f] (p : Prop) [Decidable p] : f (Inhabited p) :=
  if h : p then pure ⟨h⟩ else failure

/- Later we define a coercion from bool to Prop, but this version will still be useful.
   Given (t : tactic bool), we can write t >>= guardb -/
@[inline]
def guardb {f : Type → Type v} [Alternativeₓ f] : Bool → f Unit
  | tt => pure ()
  | ff => failure

@[inline]
def optionalₓ (x : f α) : f (Option α) :=
  some <$> x <|> pure none

end

