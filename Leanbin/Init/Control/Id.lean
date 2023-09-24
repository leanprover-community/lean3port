/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The identity monad.
-/
prelude
import Init.Control.Lift

#align_import init.control.id from "leanprover-community/lean"@"e611ee5c2bd410148bcd493c58cb17498d667175"

universe u

@[inline]
def idBind {α β : Type u} (x : α) (f : α → id β) : id β :=
  f x
#align id_bind idBind

@[inline]
instance : Monad.{u, u} id where
  pure := @id
  bind := @idBind

@[inline]
instance : MonadRun id id :=
  ⟨@id⟩

