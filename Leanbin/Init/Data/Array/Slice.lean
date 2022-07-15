/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Leanbin.Init.Data.Nat.Default
import Leanbin.Init.Data.Array.Basic
import Leanbin.Init.Data.Nat.Lemmas

universe u

variable {α : Type u} {n : Nat}

namespace Arrayₓ

def slice (a : Arrayₓ n α) (k l : Nat) (h₁ : k ≤ l) (h₂ : l ≤ n) : Arrayₓ (l - k) α :=
  ⟨fun ⟨i, hi⟩ =>
    a.read
      ⟨i + k,
        calc
          i + k < l - k + k := Nat.add_lt_add_rightₓ hi _
          _ = l := Nat.sub_add_cancelₓ h₁
          _ ≤ n := h₂
          ⟩⟩

def take (a : Arrayₓ n α) (m : Nat) (h : m ≤ n) : Arrayₓ m α :=
  cast
      (by
        simp ) <|
    a.slice 0 m (Nat.zero_leₓ _) h

def drop (a : Arrayₓ n α) (m : Nat) (h : m ≤ n) : Arrayₓ (n - m) α :=
  a.slice m n h (le_reflₓ _)

private theorem sub_sub_cancel (m n : ℕ) (h : m ≤ n) : n - (n - m) = m :=
  calc
    n - (n - m) = n - m + m - (n - m) := by
      rw [Nat.sub_add_cancelₓ] <;> assumption
    _ = m := Nat.add_sub_cancel_left _ _
    

def takeRight (a : Arrayₓ n α) (m : Nat) (h : m ≤ n) : Arrayₓ m α :=
  cast
      (by
        simp [*, ← sub_sub_cancel]) <|
    a.drop (n - m) (Nat.sub_leₓ _ _)

def reverse (a : Arrayₓ n α) : Arrayₓ n α :=
  ⟨fun ⟨i, hi⟩ =>
    a.read
      ⟨n - (i + 1), by
        apply Nat.sub_lt_of_pos_leₓ
        apply Nat.zero_lt_succₓ
        assumption⟩⟩

end Arrayₓ

