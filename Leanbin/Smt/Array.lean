/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module smt.array
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

namespace Smt

universe u v

def Array (α : Type u) (β : Type v) :=
  α → β
#align smt.array Smt.Array

variable {α : Type u} {β : Type v}

open Tactic

def select (a : Array α β) (i : α) : β :=
  a i
#align smt.select Smt.select

theorem arrayext (a₁ a₂ : Array α β) : (∀ i, select a₁ i = select a₂ i) → a₁ = a₂ :=
  funext
#align smt.arrayext Smt.arrayext

variable [DecidableEq α]

def store (a : Array α β) (i : α) (v : β) : Array α β := fun j => if j = i then v else select a j
#align smt.store Smt.store

@[simp]
theorem select_store (a : Array α β) (i : α) (v : β) : select (store a i v) i = v := by
  unfold Smt.store Smt.select <;> rw [if_pos] <;> rfl
#align smt.select_store Smt.select_store

@[simp]
theorem select_store_ne (a : Array α β) (i j : α) (v : β) :
    j ≠ i → select (store a i v) j = select a j := by
  intros <;> unfold Smt.store Smt.select <;> rw [if_neg] <;> assumption
#align smt.select_store_ne Smt.select_store_ne

end Smt

