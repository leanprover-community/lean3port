/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.punit
! leanprover-community/mathlib commit ab7b94ef22d18679460483c47458a58716eb47da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Logic

#print PUnit.subsingleton /-
theorem PUnit.subsingleton (a b : PUnit) : a = b :=
  PUnit.recOn a (PUnit.recOn b rfl)
#align punit_eq PUnit.subsingleton
-/

#print PUnit.eq_punit /-
theorem PUnit.eq_punit (a : PUnit) : a = PUnit.unit :=
  PUnit.subsingleton a PUnit.unit
#align punit_eq_star PUnit.eq_punit
-/

instance : Subsingleton PUnit :=
  Subsingleton.intro PUnit.subsingleton

instance : Inhabited PUnit :=
  ⟨PUnit.unit⟩

instance : DecidableEq PUnit := fun a b => isTrue (PUnit.subsingleton a b)

