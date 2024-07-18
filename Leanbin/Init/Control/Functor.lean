/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.Core
import Logic.Function.Defs
import Init.Meta.Name

#align_import init.control.functor from "leanprover-community/lean"@"e611ee5c2bd410148bcd493c58cb17498d667175"

open Function

universe u v

#print Functor /-
class Functor (f : Type u → Type v) : Type max (u + 1) v where
  map : ∀ {α β : Type u}, (α → β) → f α → f β
  mapConst : ∀ {α β : Type u}, α → f β → f α := fun α β => map ∘ const β
#align functor Functor
-/

infixr:100 " <$ " => Functor.mapConst

#print Functor.mapConstRev /-
@[reducible]
def Functor.mapConstRev {f : Type u → Type v} [Functor f] {α β : Type u} : f β → α → f α :=
  fun a b => b <$ a
#align functor.map_const_rev Functor.mapConstRev
-/

infixr:100 " $> " => Functor.mapConstRev

