/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Nat.Default
import Leanbin.Init.Data.Fin.Basic

namespace Finₓ

open Nat

variable {n : Nat}

protected def succ : Finₓ n → Finₓ (succ n)
  | ⟨a, h⟩ => ⟨Nat.succ a, succ_lt_succₓ h⟩

def ofNat {n : Nat} (a : Nat) : Finₓ (succ n) :=
  ⟨a % succ n, Nat.mod_ltₓ _ (Nat.zero_lt_succₓ _)⟩

private theorem mlt {n b : Nat} : ∀ {a}, n > a → b % n < n
  | 0, h => Nat.mod_ltₓ _ h
  | a + 1, h =>
    have : n > 0 := lt_transₓ (Nat.zero_lt_succₓ _) h
    Nat.mod_ltₓ _ this

protected def add : Finₓ n → Finₓ n → Finₓ n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + b) % n, mlt h⟩

protected def mul : Finₓ n → Finₓ n → Finₓ n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a * b % n, mlt h⟩

private theorem sublt {a b n : Nat} (h : a < n) : a - b < n :=
  lt_of_le_of_ltₓ (Nat.sub_leₓ a b) h

protected def sub : Finₓ n → Finₓ n → Finₓ n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + (n - b)) % n, mlt h⟩

private theorem modlt {a b n : Nat} (h₁ : a < n) (h₂ : b < n) : a % b < n := by
  cases' b with b
  · simp [mod_zero]
    assumption
    
  · have h : a % succ b < succ b
    apply Nat.mod_ltₓ _ (Nat.zero_lt_succₓ _)
    exact lt_transₓ h h₂
    

protected def mod : Finₓ n → Finₓ n → Finₓ n
  | ⟨a, h₁⟩, ⟨b, h₂⟩ => ⟨a % b, modlt h₁ h₂⟩

private theorem divlt {a b n : Nat} (h : a < n) : a / b < n :=
  lt_of_le_of_ltₓ (Nat.div_le_selfₓ a b) h

protected def div : Finₓ n → Finₓ n → Finₓ n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a / b, divlt h⟩

instance : Zero (Finₓ (succ n)) :=
  ⟨⟨0, succ_posₓ n⟩⟩

instance : One (Finₓ (succ n)) :=
  ⟨ofNat 1⟩

instance : Add (Finₓ n) :=
  ⟨Finₓ.add⟩

instance : Sub (Finₓ n) :=
  ⟨Finₓ.sub⟩

instance : Mul (Finₓ n) :=
  ⟨Finₓ.mul⟩

instance : Mod (Finₓ n) :=
  ⟨Finₓ.mod⟩

instance : Div (Finₓ n) :=
  ⟨Finₓ.div⟩

theorem of_nat_zero : @ofNat n 0 = 0 :=
  rfl

theorem add_def (a b : Finₓ n) : (a + b).val = (a.val + b.val) % n :=
  show (Finₓ.add a b).val = (a.val + b.val) % n by
    cases a <;> cases b <;> simp [Finₓ.add]

theorem mul_def (a b : Finₓ n) : (a * b).val = a.val * b.val % n :=
  show (Finₓ.mul a b).val = a.val * b.val % n by
    cases a <;> cases b <;> simp [Finₓ.mul]

theorem sub_def (a b : Finₓ n) : (a - b).val = (a.val + (n - b.val)) % n := by
  cases a <;> cases b <;> rfl

theorem mod_def (a b : Finₓ n) : (a % b).val = a.val % b.val :=
  show (Finₓ.mod a b).val = a.val % b.val by
    cases a <;> cases b <;> simp [Finₓ.mod]

theorem div_def (a b : Finₓ n) : (a / b).val = a.val / b.val :=
  show (Finₓ.div a b).val = a.val / b.val by
    cases a <;> cases b <;> simp [Finₓ.div]

theorem lt_def (a b : Finₓ n) : (a < b) = (a.val < b.val) :=
  show Finₓ.Lt a b = (a.val < b.val) by
    cases a <;> cases b <;> simp [Finₓ.Lt]

theorem le_def (a b : Finₓ n) : (a ≤ b) = (a.val ≤ b.val) :=
  show Finₓ.Le a b = (a.val ≤ b.val) by
    cases a <;> cases b <;> simp [Finₓ.Le]

theorem val_zero : (0 : Finₓ (succ n)).val = 0 :=
  rfl

def pred {n : Nat} : ∀ i : Finₓ (succ n), i ≠ 0 → Finₓ n
  | ⟨a, h₁⟩, h₂ =>
    ⟨a.pred, by
      have : a ≠ 0 := by
        have aux₁ := vne_of_ne h₂
        dsimp'  at aux₁
        rw [val_zero] at aux₁
        exact aux₁
      exact Nat.pred_lt_predₓ this h₁⟩

end Finₓ

