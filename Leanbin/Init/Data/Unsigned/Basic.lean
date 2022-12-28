/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.unsigned.basic
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Fin.Basic

open Nat

def unsignedSz : Nat :=
  succ 4294967295
#align unsigned_sz unsignedSz

def Unsigned :=
  Fin unsignedSz
#align unsigned Unsigned

namespace Unsigned

-- We cannot use tactic dec_trivial here because the tactic framework has not been defined yet.
private theorem zero_lt_unsigned_sz : 0 < unsignedSz :=
  zero_lt_succ _
#align unsigned.zero_lt_unsigned_sz unsigned.zero_lt_unsigned_sz

-- Later, we define of_nat using mod, the following version is used to define the metaprogramming system.
protected def ofNat' (n : Nat) : Unsigned :=
  if h : n < unsignedSz then ⟨n, h⟩ else ⟨0, zero_lt_unsigned_sz⟩
#align unsigned.of_nat' Unsigned.ofNat'

def toNat (c : Unsigned) : Nat :=
  c.val
#align unsigned.to_nat Unsigned.toNat

end Unsigned

instance : DecidableEq Unsigned :=
  have : DecidableEq (Fin unsignedSz) := Fin.decidableEq _
  this

