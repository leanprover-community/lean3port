/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Nat.Default
import Leanbin.Init.Data.Fin.Basic

namespace Fin

open Nat

theorem of_nat_zero : @Fin.ofNat n 0 = 0 :=
  rfl

theorem div_def (a b : Fin n) : (a / b).val = a.val / b.val := by
  show (a.val / b.val) % n = a.val / b.val
  rw [Nat.mod_eq_of_lt]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) a.2

theorem lt_def (a b : Fin n) : (a < b) = (a.val < b.val) :=
  rfl

theorem le_def (a b : Fin n) : (a ≤ b) = (a.val ≤ b.val) :=
  rfl

theorem val_zero : (0 : Fin (n + 1)).val = 0 := by
  simp

def pred {n : Nat} : ∀ i : Fin (n + 1), i ≠ 0 → Fin n
  | ⟨a, h₁⟩, h₂ =>
    ⟨a.pred, by
      have : a ≠ 0 := by
        have aux₁ := vne_of_ne h₂
        dsimp at aux₁
        rw [val_zero] at aux₁
        exact aux₁
      exact Nat.pred_lt_pred this h₁⟩

end Fin

