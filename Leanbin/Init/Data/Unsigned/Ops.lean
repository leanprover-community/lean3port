prelude
import Leanbin.Init.Data.Unsigned.Basic
import Leanbin.Init.Data.Fin.Ops

namespace Unsigned

def of_nat (n : Nat) : Unsigned :=
  Finₓ.ofNat n

instance : HasZero Unsigned :=
  ⟨Finₓ.ofNat 0⟩

instance : HasOne Unsigned :=
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

