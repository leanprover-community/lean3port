/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.fin.ops
! leanprover-community/lean commit 3d2e3b75617386cb32de6cbc7e1cd341c6a16adf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Nat.Default
import Leanbin.Init.Data.Fin.Basic

namespace Fin

open Nat

variable {n : Nat}

#print Fin.succ /-
protected def succ : Fin n → Fin (succ n)
  | ⟨a, h⟩ => ⟨Nat.succ a, succ_lt_succ h⟩
#align fin.succ Fin.succ
-/

#print Fin.ofNat /-
def ofNat {n : Nat} (a : Nat) : Fin (succ n) :=
  ⟨a % succ n, Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
#align fin.of_nat Fin.ofNat
-/

private theorem mlt {n b : Nat} : ∀ {a}, n > a → b % n < n
  | 0, h => Nat.mod_lt _ h
  | a + 1, h =>
    have : n > 0 := lt_trans (Nat.zero_lt_succ _) h
    Nat.mod_lt _ this

#print Fin.add /-
protected def add : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + b) % n, mlt h⟩
#align fin.add Fin.add
-/

#print Fin.mul /-
protected def mul : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a * b % n, mlt h⟩
#align fin.mul Fin.mul
-/

private theorem sublt {a b n : Nat} (h : a < n) : a - b < n :=
  lt_of_le_of_lt (Nat.sub_le a b) h

#print Fin.sub /-
protected def sub : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + (n - b)) % n, mlt h⟩
#align fin.sub Fin.sub
-/

private theorem modlt {a b n : Nat} (h₁ : a < n) (h₂ : b < n) : a % b < n :=
  by
  cases' b with b
  · simp [mod_zero]; assumption
  · have h : a % succ b < succ b
    apply Nat.mod_lt _ (Nat.zero_lt_succ _)
    exact lt_trans h h₂

#print Fin.mod /-
protected def mod : Fin n → Fin n → Fin n
  | ⟨a, h₁⟩, ⟨b, h₂⟩ => ⟨a % b, modlt h₁ h₂⟩
#align fin.mod Fin.mod
-/

private theorem divlt {a b n : Nat} (h : a < n) : a / b < n :=
  lt_of_le_of_lt (Nat.div_le_self a b) h

#print Fin.div /-
protected def div : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a / b, divlt h⟩
#align fin.div Fin.div
-/

instance : Zero (Fin (succ n)) :=
  ⟨⟨0, succ_pos n⟩⟩

instance : One (Fin (succ n)) :=
  ⟨ofNat 1⟩

instance : Add (Fin n) :=
  ⟨Fin.add⟩

instance : Sub (Fin n) :=
  ⟨Fin.sub⟩

instance : Mul (Fin n) :=
  ⟨Fin.mul⟩

instance : Mod (Fin n) :=
  ⟨Fin.mod⟩

instance : Div (Fin n) :=
  ⟨Fin.div⟩

theorem ofNat_zero : @ofNat n 0 = 0 :=
  rfl
#align fin.of_nat_zero Fin.ofNat_zero

theorem add_def (a b : Fin n) : (a + b).val = (a.val + b.val) % n :=
  show (Fin.add a b).val = (a.val + b.val) % n by cases a <;> cases b <;> simp [Fin.add]
#align fin.add_def Fin.add_def

theorem mul_def (a b : Fin n) : (a * b).val = a.val * b.val % n :=
  show (Fin.mul a b).val = a.val * b.val % n by cases a <;> cases b <;> simp [Fin.mul]
#align fin.mul_def Fin.mul_def

theorem sub_def (a b : Fin n) : (a - b).val = (a.val + (n - b.val)) % n := by
  cases a <;> cases b <;> rfl
#align fin.sub_def Fin.sub_def

theorem mod_def (a b : Fin n) : (a % b).val = a.val % b.val :=
  show (Fin.mod a b).val = a.val % b.val by cases a <;> cases b <;> simp [Fin.mod]
#align fin.mod_def Fin.mod_def

theorem div_def (a b : Fin n) : (a / b).val = a.val / b.val :=
  show (Fin.div a b).val = a.val / b.val by cases a <;> cases b <;> simp [Fin.div]
#align fin.div_def Fin.div_def

theorem lt_def (a b : Fin n) : (a < b) = (a.val < b.val) :=
  show Fin.Lt a b = (a.val < b.val) by cases a <;> cases b <;> simp [Fin.Lt]
#align fin.lt_def Fin.lt_def

theorem le_def (a b : Fin n) : (a ≤ b) = (a.val ≤ b.val) :=
  show Fin.Le a b = (a.val ≤ b.val) by cases a <;> cases b <;> simp [Fin.Le]
#align fin.le_def Fin.le_def

/- warning: fin.val_zero clashes with fin.coe_zero -> Fin.val_zero
Case conversion may be inaccurate. Consider using '#align fin.val_zero Fin.val_zeroₓ'. -/
theorem val_zero : (0 : Fin (succ n)).val = 0 :=
  rfl
#align fin.val_zero Fin.val_zero

#print Fin.pred /-
def pred {n : Nat} : ∀ i : Fin (succ n), i ≠ 0 → Fin n
  | ⟨a, h₁⟩, h₂ =>
    ⟨a.pred,
      haveI : a ≠ 0 := by
        have aux₁ := vne_of_ne h₂
        dsimp at aux₁; rw [val_zero] at aux₁; exact aux₁
      Nat.pred_lt_pred this h₁⟩
#align fin.pred Fin.pred
-/

end Fin

