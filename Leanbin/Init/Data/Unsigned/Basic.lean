/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Fin.Basic

open Nat

def unsignedSz : Nat :=
  succ 4294967295

def Unsigned :=
  Finₓ unsignedSz

namespace Unsigned

-- We cannot use tactic dec_trivial here because the tactic framework has not been defined yet.
private theorem zero_lt_unsigned_sz : 0 < unsignedSz :=
  zero_lt_succₓ _

-- Later, we define of_nat using mod, the following version is used to define the metaprogramming system.
protected def ofNat' (n : Nat) : Unsigned :=
  if h : n < unsignedSz then ⟨n, h⟩ else ⟨0, zero_lt_unsigned_sz⟩

def toNat (c : Unsigned) : Nat :=
  c.val

end Unsigned

instance : DecidableEq Unsigned :=
  have : DecidableEq (Finₓ unsignedSz) := Finₓ.decidableEq _
  this

