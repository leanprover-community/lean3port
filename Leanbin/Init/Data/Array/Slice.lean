/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner

! This file was ported from Lean 3 source module init.data.array.slice
! leanprover-community/mathlib commit 194cc8e2416b5969cfdab4006bb9e20cb75e5adc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Nat.Default
import Leanbin.Init.Data.Array.Basic
import Leanbin.Init.Data.Nat.Lemmas

universe u

variable {α : Type u} {n : Nat}

namespace Array'

def slice (a : Array' n α) (k l : Nat) (h₁ : k ≤ l) (h₂ : l ≤ n) : Array' (l - k) α :=
  ⟨fun ⟨i, hi⟩ =>
    a.read
      ⟨i + k,
        calc
          i + k < l - k + k := Nat.add_lt_add_right hi _
          _ = l := Nat.sub_add_cancel h₁
          _ ≤ n := h₂
          ⟩⟩
#align array.slice Array'.slice

def take (a : Array' n α) (m : Nat) (h : m ≤ n) : Array' m α :=
  cast (by simp) <| a.slice 0 m (Nat.zero_le _) h
#align array.take Array'.take

def drop (a : Array' n α) (m : Nat) (h : m ≤ n) : Array' (n - m) α :=
  a.slice m n h (le_refl _)
#align array.drop Array'.drop

private theorem sub_sub_cancel (m n : ℕ) (h : m ≤ n) : n - (n - m) = m :=
  calc
    n - (n - m) = n - m + m - (n - m) := by rw [Nat.sub_add_cancel] <;> assumption
    _ = m := Nat.add_sub_cancel_left _ _
    
#align array.sub_sub_cancel array.sub_sub_cancel

def takeRight (a : Array' n α) (m : Nat) (h : m ≤ n) : Array' m α :=
  cast (by simp [*, sub_sub_cancel]) <| a.drop (n - m) (Nat.sub_le _ _)
#align array.take_right Array'.takeRight

def reverse (a : Array' n α) : Array' n α :=
  ⟨fun ⟨i, hi⟩ =>
    a.read ⟨n - (i + 1), by apply Nat.sub_lt_of_pos_le; apply Nat.zero_lt_succ; assumption⟩⟩
#align array.reverse Array'.reverse

end Array'

