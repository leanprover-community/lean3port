/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Nat.Basic

open Nat

namespace Fin

variable {n : Nat}

theorem eq_of_veq : ∀ {i j : Fin n}, i.val = j.val → i = j
  | ⟨iv, ilt₁⟩, ⟨_, ilt₂⟩, rfl => rfl

theorem veq_of_eq : ∀ {i j : Fin n}, i = j → i.val = j.val
  | ⟨iv, ilt⟩, _, rfl => rfl

theorem ne_of_vne {i j : Fin n} (h : i.val ≠ j.val) : i ≠ j := fun h' => absurd (veq_of_eq h') h

theorem vne_of_ne {i j : Fin n} (h : i ≠ j) : i.val ≠ j.val := fun h' => absurd (eq_of_veq h') h

end Fin

