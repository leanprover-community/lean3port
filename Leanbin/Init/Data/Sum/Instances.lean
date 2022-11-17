/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.MkDecEqInstance

universe u v

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic tactic.mk_dec_eq_instance -/
instance {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] : DecidableEq (α ⊕ β) := by
  run_tac
    tactic.mk_dec_eq_instance

