/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.MkDecEqInstance
import Leanbin.Init.Data.Subtype.Basic

open Tactic Subtype

universe u

instance {α : Type u} {p : α → Prop} [DecidableEq α] : DecidableEq { x : α // p x } := by
  run_tac
    mk_dec_eq_instance

