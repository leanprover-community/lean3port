/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta.MkDecEqInstance

#align_import init.data.sum.instances from "leanprover-community/lean"@"32e6442d0a1c9ab6948d5aaf6dc1de98a3d282e4"

universe u v

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.mk_dec_eq_instance -/
instance {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] : DecidableEq (Sum α β) := by
  run_tac
    tactic.mk_dec_eq_instance

