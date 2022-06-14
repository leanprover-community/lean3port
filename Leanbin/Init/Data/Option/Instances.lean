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

instance : IsLawfulMonad Option where
  id_map := fun α x => Option.rec rfl (fun x => rfl) x
  pure_bind := fun α β x f => rfl
  bind_assoc := fun α β γ x f g => Option.rec rfl (fun x => rfl) x

theorem Option.eq_of_eq_some {α : Type u} : ∀ {x y : Option α}, (∀ z, x = some z ↔ y = some z) → x = y
  | none, none, h => rfl
  | none, some z, h => Option.noConfusion ((h z).2 rfl)
  | some z, none, h => Option.noConfusion ((h z).1 rfl)
  | some z, some w, h => Option.noConfusion ((h w).2 rfl) (congr_arg some)

theorem Option.eq_some_of_is_some {α : Type u} : ∀ {o : Option α} h : Option.isSome o, o = some (Option.getₓ h)
  | some x, h => rfl

theorem Option.eq_none_of_is_none {α : Type u} : ∀ {o : Option α}, o.isNone → o = none
  | none, h => rfl

