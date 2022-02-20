/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import Leanbin.Init.Control.Applicative

universe u v

open Function

class Bind (m : Type u → Type v) where
  bind : ∀ {α β : Type u}, m α → (α → m β) → m β

export Bind (bind)

@[inline]
def Bind.andThen {α β : Type u} {m : Type u → Type v} [Bind m] (x : m α) (y : m β) : m β := do
  x
  y

class Monadₓ (m : Type u → Type v) extends Applicativeₓ m, Bind m : Type max (u + 1) v where
  map := fun α β f x => x >>= pure ∘ f
  seq := fun α β f x => f >>= (· <$> x)

@[reducible, inline]
def return {m : Type u → Type v} [Monadₓ m] {α : Type u} : α → m α :=
  pure

-- Identical to has_bind.and_then, but it is not inlined.
def Bind.seq {α β : Type u} {m : Type u → Type v} [Bind m] (x : m α) (y : m β) : m β := do
  x
  y

