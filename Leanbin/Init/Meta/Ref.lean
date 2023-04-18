/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.ref
! leanprover-community/lean commit e29c19c1aa04f5442d3bd035902705f50486c67a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Tactic

universe u v

namespace Tactic

/-- A `ref` performs the role of a mutable variable within a tactic. -/
unsafe axiom ref (α : Type u) : Type u
#align tactic.ref tactic.ref

/-- Create a new reference `r` with initial value `a`, execute `t r`, and then delete `r`. -/
unsafe axiom using_new_ref {α : Type u} {β : Type v} (a : α) (t : ref α → tactic β) : tactic β
#align tactic.using_new_ref tactic.using_new_ref

/-- Read the value stored in the given reference. -/
unsafe axiom read_ref {α : Type u} : ref α → tactic α
#align tactic.read_ref tactic.read_ref

/-- Update the value stored in the given reference. -/
unsafe axiom write_ref {α : Type u} : ref α → α → tactic Unit
#align tactic.write_ref tactic.write_ref

end Tactic

