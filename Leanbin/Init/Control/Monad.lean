/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import Leanbin.Init.Control.Applicative

#align_import init.control.monad from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

universe u v

open Function

#print Bind /-
class Bind (m : Type u → Type v) where
  bind : ∀ {α β : Type u}, m α → (α → m β) → m β
#align has_bind Bind
-/

export Bind (bind)

@[inline]
def Bind.andThen {α β : Type u} {m : Type u → Type v} [Bind m] (x : m α) (y : m β) : m β := do
  x
  y
#align has_bind.and_then Bind.andThen

#print Monad /-
class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type max (u + 1) v where
  map := fun α β f x => x >>= pure ∘ f
  seq := fun α β f x => f >>= (· <$> x)
#align monad Monad
-/

@[reducible, inline]
def return {m : Type u → Type v} [Monad m] {α : Type u} : α → m α :=
  pure
#align return return

/-- Identical to `has_bind.and_then`, but it is not inlined. -/
def Bind.seq {α β : Type u} {m : Type u → Type v} [Bind m] (x : m α) (y : m β) : m β := do
  x
  y
#align has_bind.seq Bind.seq

