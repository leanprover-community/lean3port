/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import Leanbin.Init.Control.Applicative

universe u v

open Function

@[inline]
def Bind.andThen {α β : Type u} {m : Type u → Type v} [Bind m] (x : m α) (y : m β) : m β :=
  x >>= fun _ => y

@[reducible, inline]
def «return» {m : Type u → Type v} [Monad m] {α : Type u} : α → m α :=
  pure

-- Identical to has_bind.and_then, but it is not inlined.
def Bind.seq {α β : Type u} {m : Type u → Type v} [Bind m] (x : m α) (y : m β) : m β := do
  Bind.andThen x y

