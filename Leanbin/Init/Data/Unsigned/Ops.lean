/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.unsigned.ops
! leanprover-community/lean commit 0049a42336d64521ef60cc4c079fd4108b37680c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Unsigned.Basic
import Leanbin.Init.Data.Fin.Ops

namespace Unsigned

def ofNat (n : Nat) : Unsigned :=
  Fin.ofNat n
#align unsigned.of_nat Unsigned.ofNat

instance : Zero Unsigned :=
  ⟨Fin.ofNat 0⟩

instance : One Unsigned :=
  ⟨Fin.ofNat 1⟩

instance : Add Unsigned :=
  ⟨Fin.add⟩

instance : Sub Unsigned :=
  ⟨Fin.sub⟩

instance : Mul Unsigned :=
  ⟨Fin.mul⟩

instance : Mod Unsigned :=
  ⟨Fin.mod⟩

instance : Div Unsigned :=
  ⟨Fin.div⟩

instance : LT Unsigned :=
  ⟨Fin.Lt⟩

instance : LE Unsigned :=
  ⟨Fin.Le⟩

end Unsigned

