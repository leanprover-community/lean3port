/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Meta.MkDecEqInstance
import Init.Data.Subtype.Basic

#align_import init.data.subtype.instances from "leanprover-community/lean"@"32e6442d0a1c9ab6948d5aaf6dc1de98a3d282e4"

open Tactic Subtype

universe u

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.mk_dec_eq_instance -/
instance {α : Type u} {p : α → Prop} [DecidableEq α] : DecidableEq { x : α // p x } := by
  run_tac
    mk_dec_eq_instance

