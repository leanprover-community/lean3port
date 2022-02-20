/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Tactic

universe u v

namespace Tactic

/-- A `ref` performs the role of a mutable variable within a tactic. -/
unsafe axiom ref (α : Type u) : Type u

/-- Create a new reference `r` with initial value `a`, execute `t r`, and then delete `r`. -/
unsafe axiom using_new_ref {α : Type u} {β : Type v} (a : α) (t : ref α → tactic β) : tactic β

/-- Read the value stored in the given reference. -/
unsafe axiom read_ref {α : Type u} : ref α → tactic α

/-- Update the value stored in the given reference. -/
unsafe axiom write_ref {α : Type u} : ref α → α → tactic Unit

end Tactic

