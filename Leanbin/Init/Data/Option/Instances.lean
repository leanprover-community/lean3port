/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Option.Basic
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Control.Lawful

universe u v

theorem Option.eq_some_of_is_some {α : Type u} : ∀ {o : Option α} (h : Option.isSome o), o = some (Option.get h)
  | some x, h => rfl

theorem Option.eq_none_of_is_none {α : Type u} : ∀ {o : Option α}, o.isNone → o = none
  | none, h => rfl

