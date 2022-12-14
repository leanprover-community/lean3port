/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.subtype.instances
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.MkDecEqInstance
import Leanbin.Init.Data.Subtype.Basic

open Tactic Subtype

universe u

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:61:18: unsupported non-interactive tactic tactic.mk_dec_eq_instance -/
instance {α : Type u} {p : α → Prop} [DecidableEq α] : DecidableEq { x : α // p x } := by
  run_tac
    mk_dec_eq_instance

