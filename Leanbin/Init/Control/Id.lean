/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The identity monad.
-/
prelude
import Leanbin.Init.Control.Lift

universe u

@[inline]
def idBind {α β : Type u} (x : α) (f : α → id β) : id β :=
  f x

@[inline]
instance : Monadₓ.{u, u} id where
  pure := @id
  bind := @idBind

@[inline]
instance : MonadRun id id :=
  ⟨@id⟩

