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
  Fin.ofNat n

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
  inferInstanceAs (LT (Fin _))

instance : LE Unsigned :=
  inferInstanceAs (LE (Fin _))

end Unsigned

