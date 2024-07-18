/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Option.Basic
import Init.Meta.Tactic
import Control.Lawful

#align_import init.data.option.instances from "leanprover-community/lean"@"e611ee5c2bd410148bcd493c58cb17498d667175"

universe u v

instance : LawfulMonad Option
    where
  id_map α x := Option.rec rfl (fun x => rfl) x
  pure_bind α β x f := rfl
  bind_assoc α β γ x f g := Option.rec rfl (fun x => rfl) x

#print Option.eq_of_eq_some /-
theorem Option.eq_of_eq_some {α : Type u} :
    ∀ {x y : Option α}, (∀ z, x = some z ↔ y = some z) → x = y
  | none, none, h => rfl
  | none, some z, h => Option.noConfusion ((h z).2 rfl)
  | some z, none, h => Option.noConfusion ((h z).1 rfl)
  | some z, some w, h => Option.noConfusion ((h w).2 rfl) (congr_arg some)
#align option.eq_of_eq_some Option.eq_of_eq_some
-/

#print Option.eq_some_of_isSome /-
theorem Option.eq_some_of_isSome {α : Type u} :
    ∀ {o : Option α} (h : Option.isSome o), o = some (Option.get h)
  | some x, h => rfl
#align option.eq_some_of_is_some Option.eq_some_of_isSome
-/

#print Option.eq_none_of_isNone /-
theorem Option.eq_none_of_isNone {α : Type u} : ∀ {o : Option α}, o.isNone → o = none
  | none, h => rfl
#align option.eq_none_of_is_none Option.eq_none_of_isNone
-/

