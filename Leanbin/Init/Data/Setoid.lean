/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic

universe u

class Setoid (α : Sort u) where
  R : α → α → Prop
  iseqv : Equivalence r

instance (priority := 100) setoidHasEquiv {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.R⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

@[refl]
theorem refl (a : α) : a ≈ a :=
  match Setoid.iseqv with
  | ⟨h_refl, h_symm, h_trans⟩ => h_refl a

@[symm]
theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  match Setoid.iseqv with
  | ⟨h_refl, h_symm, h_trans⟩ => h_symm hab

@[trans]
theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  match Setoid.iseqv with
  | ⟨h_refl, h_symm, h_trans⟩ => h_trans hab hbc

end Setoid

