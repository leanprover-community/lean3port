/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.MkDecEqInstance

universe u v

instance {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] : DecidableEq (Sum α β) := by
  run_tac
    tactic.mk_dec_eq_instance

