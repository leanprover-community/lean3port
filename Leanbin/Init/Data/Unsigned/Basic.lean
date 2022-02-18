prelude
import Leanbin.Init.Data.Fin.Basic

open Nat

def unsignedSz : Nat :=
  succ 4294967295

def Unsigned :=
  Finₓ unsignedSz

namespace Unsigned

private theorem zero_lt_unsigned_sz : 0 < unsignedSz :=
  zero_lt_succₓ _

protected def of_nat' (n : Nat) : Unsigned :=
  if h : n < unsignedSz then ⟨n, h⟩ else ⟨0, zero_lt_unsigned_sz⟩

def to_nat (c : Unsigned) : Nat :=
  c.val

end Unsigned

instance : DecidableEq Unsigned :=
  have : DecidableEq (Finₓ unsignedSz) := Finₓ.decidableEq _
  this

