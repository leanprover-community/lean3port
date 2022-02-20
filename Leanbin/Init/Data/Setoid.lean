/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic

universe u

class Setoidₓ (α : Sort u) where
  R : α → α → Prop
  iseqv : Equivalenceₓ r

instance (priority := 100) setoidHasEquiv {α : Sort u} [Setoidₓ α] : HasEquivₓ α :=
  ⟨Setoidₓ.R⟩

namespace Setoidₓ

variable {α : Sort u} [Setoidₓ α]

@[refl]
theorem refl (a : α) : a ≈ a :=
  match Setoidₓ.iseqv with
  | ⟨h_refl, h_symm, h_trans⟩ => h_refl a

@[symm]
theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  match Setoidₓ.iseqv with
  | ⟨h_refl, h_symm, h_trans⟩ => h_symm hab

@[trans]
theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  match Setoidₓ.iseqv with
  | ⟨h_refl, h_symm, h_trans⟩ => h_trans hab hbc

end Setoidₓ

