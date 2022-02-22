/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Leanbin.Init.Core
import Leanbin.Init.Function
import Leanbin.Init.Meta.Name

open Function

universe u v

class Functor (f : Type u → Type v) : Type max (u + 1) v where
  map : ∀ {α β : Type u}, (α → β) → f α → f β
  mapConst : ∀ {α β : Type u}, α → f β → f α := fun α β => map ∘ const β

-- mathport name: «expr <$ »
infixr:100 " <$ " => Functor.mapConst

@[reducible]
def Functor.mapConstRev {f : Type u → Type v} [Functor f] {α β : Type u} : f β → α → f α := fun a b => b <$ a

-- mathport name: «expr $> »
infixr:100 " $> " => Functor.mapConstRev

