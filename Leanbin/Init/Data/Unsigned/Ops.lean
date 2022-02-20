/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Unsigned.Basic
import Leanbin.Init.Data.Fin.Ops

namespace Unsigned

def ofNat (n : Nat) : Unsigned :=
  Finₓ.ofNat n

instance : Zero Unsigned :=
  ⟨Finₓ.ofNat 0⟩

instance : One Unsigned :=
  ⟨Finₓ.ofNat 1⟩

instance : Add Unsigned :=
  ⟨Finₓ.add⟩

instance : Sub Unsigned :=
  ⟨Finₓ.sub⟩

instance : Mul Unsigned :=
  ⟨Finₓ.mul⟩

instance : Mod Unsigned :=
  ⟨Finₓ.mod⟩

instance : Div Unsigned :=
  ⟨Finₓ.div⟩

instance : LT Unsigned :=
  ⟨Finₓ.Lt⟩

instance : LE Unsigned :=
  ⟨Finₓ.Le⟩

end Unsigned

