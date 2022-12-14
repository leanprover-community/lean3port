/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.setoid
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Logic

universe u

#print Setoid /-
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r
#align setoid Setoid
-/

instance (priority := 100) setoidHasEquiv {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩
#align setoid_has_equiv setoidHasEquiv

namespace Setoid

variable {α : Sort u} [Setoid α]

#print Setoid.refl /-
@[refl]
theorem refl (a : α) : a ≈ a :=
  match Setoid.iseqv with
  | ⟨h_refl, h_symm, h_trans⟩ => h_refl a
#align setoid.refl Setoid.refl
-/

#print Setoid.symm /-
@[symm]
theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  match Setoid.iseqv with
  | ⟨h_refl, h_symm, h_trans⟩ => h_symm hab
#align setoid.symm Setoid.symm
-/

#print Setoid.trans /-
@[trans]
theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  match Setoid.iseqv with
  | ⟨h_refl, h_symm, h_trans⟩ => h_trans hab hbc
#align setoid.trans Setoid.trans
-/

end Setoid

