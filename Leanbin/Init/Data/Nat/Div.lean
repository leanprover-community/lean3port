/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.nat.div
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Nat.Basic

namespace Nat

protected def divCore (y : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, x => if h : 0 < y ∧ y ≤ x then div_core fuel (x - y) + 1 else 0
#align nat.div_core Nat.divCore

#print Nat.div /-
protected def div (x y : ℕ) : ℕ :=
  Nat.divCore y x x
#align nat.div Nat.div
-/

instance : Div Nat :=
  ⟨Nat.div⟩

/- warning: nat.mod_core -> Nat.modCore is a dubious translation:
lean 3 declaration is
  Nat -> Nat -> Nat -> Nat
but is expected to have type
  ([mdata borrowed:1 Nat]) -> ([mdata borrowed:1 Nat]) -> Nat
Case conversion may be inaccurate. Consider using '#align nat.mod_core Nat.modCoreₓ'. -/
protected def modCore (y : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x => if h : 0 < y ∧ y ≤ x then mod_core fuel (x - y) else x
#align nat.mod_core Nat.modCore

#print Nat.mod /-
protected def mod (x y : ℕ) : ℕ :=
  Nat.modCore y x x
#align nat.mod Nat.mod
-/

instance : Mod Nat :=
  ⟨Nat.mod⟩

end Nat

