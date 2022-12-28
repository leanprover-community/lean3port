/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.subtype.instances
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.MkDecEqInstance
import Leanbin.Init.Data.Subtype.Basic

open Tactic Subtype

universe u

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_dec_eq_instance -/
instance {α : Type u} {p : α → Prop} [DecidableEq α] : DecidableEq { x : α // p x } := by
  run_tac
    mk_dec_eq_instance

