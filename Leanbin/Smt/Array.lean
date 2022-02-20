/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

namespace Smt

universe u v

def Array (α : Type u) (β : Type v) :=
  α → β

variable {α : Type u} {β : Type v}

open Tactic

def select (a : Array α β) (i : α) : β :=
  a i

theorem arrayext (a₁ a₂ : Array α β) : (∀ i, select a₁ i = select a₂ i) → a₁ = a₂ :=
  funext

variable [DecidableEq α]

def store (a : Array α β) (i : α) (v : β) : Array α β := fun j => if j = i then v else select a j

@[simp]
theorem select_store (a : Array α β) (i : α) (v : β) : select (store a i v) i = v := by
  unfold Smt.store Smt.select <;> rw [if_pos] <;> rfl

@[simp]
theorem select_store_ne (a : Array α β) (i j : α) (v : β) : j ≠ i → select (store a i v) j = select a j := by
  intros <;> unfold Smt.store Smt.select <;> rw [if_neg] <;> assumption

end Smt

