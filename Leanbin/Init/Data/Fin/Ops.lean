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

variable {n : Nat}

protected def succ : Fin n → Fin (succ n)
  | ⟨a, h⟩ => ⟨Nat.succ a, succ_lt_succ h⟩

def ofNat {n : Nat} (a : Nat) : Fin (succ n) :=
  ⟨a % succ n, Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

private theorem mlt {n b : Nat} : ∀ {a}, n > a → b % n < n
  | 0, h => Nat.mod_lt _ h
  | a + 1, h =>
    have : n > 0 := lt_trans (Nat.zero_lt_succ _) h
    Nat.mod_lt _ this

protected def add : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + b) % n, mlt h⟩

protected def mul : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a * b % n, mlt h⟩

private theorem sublt {a b n : Nat} (h : a < n) : a - b < n :=
  lt_of_le_of_lt (Nat.sub_le a b) h

protected def sub : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + (n - b)) % n, mlt h⟩

private theorem modlt {a b n : Nat} (h₁ : a < n) (h₂ : b < n) : a % b < n := by
  cases' b with b
  · simp [mod_zero]
    assumption
    
  · have h : a % succ b < succ b
    apply Nat.mod_lt _ (Nat.zero_lt_succ _)
    exact lt_trans h h₂
    

protected def mod : Fin n → Fin n → Fin n
  | ⟨a, h₁⟩, ⟨b, h₂⟩ => ⟨a % b, modlt h₁ h₂⟩

private theorem divlt {a b n : Nat} (h : a < n) : a / b < n :=
  lt_of_le_of_lt (Nat.div_le_self a b) h

protected def div : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a / b, divlt h⟩

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

theorem of_nat_zero : @ofNat n 0 = 0 :=
  rfl

/- warning: fin.add_def -> Fin.add_def is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fin.val n (HAdd.hAdd.{0 0 0} (Fin n) (Fin n) (Fin n) (instHAdd.{0} (Fin n) (Fin.hasAdd n)) a b)) (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Fin.val n a) (Fin.val n b)) n)
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Fin n) (HAdd.hAdd.{0 0 0} (Fin n) (Fin n) (Fin n) (instHAdd.{0} (Fin n) (Fin.instAddFin n)) a b) (Fin.mk n (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n a) (Fin.val n b)) n) (Nat.mod_lt (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n a) (Fin.val n b)) n (Fin.size_positive n a)))
Case conversion may be inaccurate. Consider using '#align fin.add_def Fin.add_defₓ'. -/
theorem add_def (a b : Fin n) : (a + b).val = (a.val + b.val) % n :=
  show (Fin.add a b).val = (a.val + b.val) % n by cases a <;> cases b <;> simp [Fin.add]

/- warning: fin.mul_def -> Fin.mul_def is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fin.val n (HMul.hMul.{0 0 0} (Fin n) (Fin n) (Fin n) (instHMul.{0} (Fin n) (Fin.hasMul n)) a b)) (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (HMul.hMul.{0 0 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Fin.val n a) (Fin.val n b)) n)
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Fin n) (HMul.hMul.{0 0 0} (Fin n) (Fin n) (Fin n) (instHMul.{0} (Fin n) (Fin.instMulFin n)) a b) (Fin.mk n (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (HMul.hMul.{0 0 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Fin.val n a) (Fin.val n b)) n) (Nat.mod_lt (HMul.hMul.{0 0 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Fin.val n a) (Fin.val n b)) n (Fin.size_positive n a)))
Case conversion may be inaccurate. Consider using '#align fin.mul_def Fin.mul_defₓ'. -/
theorem mul_def (a b : Fin n) : (a * b).val = a.val * b.val % n :=
  show (Fin.mul a b).val = a.val * b.val % n by cases a <;> cases b <;> simp [Fin.mul]

/- warning: fin.sub_def -> Fin.sub_def is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fin.val n (HSub.hSub.{0 0 0} (Fin n) (Fin n) (Fin n) (instHSub.{0} (Fin n) (Fin.hasSub n)) a b)) (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Fin.val n a) (HSub.hSub.{0 0 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (Fin.val n b))) n)
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Fin n) (HSub.hSub.{0 0 0} (Fin n) (Fin n) (Fin n) (instHSub.{0} (Fin n) (Fin.instSubFin n)) a b) (Fin.mk n (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n a) (HSub.hSub.{0 0 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (Fin.val n b))) n) (Nat.mod_lt (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n a) (HSub.hSub.{0 0 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (Fin.val n b))) n (Fin.size_positive n a)))
Case conversion may be inaccurate. Consider using '#align fin.sub_def Fin.sub_defₓ'. -/
theorem sub_def (a b : Fin n) : (a - b).val = (a.val + (n - b.val)) % n := by cases a <;> cases b <;> rfl

/- warning: fin.mod_def -> Fin.mod_def is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fin.val n (HMod.hMod.{0 0 0} (Fin n) (Fin n) (Fin n) (instHMod.{0} (Fin n) (Fin.hasMod n)) a b)) (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (Fin.val n a) (Fin.val n b))
but is expected to have type
  forall {n : Nat} (a : Fin n) (m : Fin n), Eq.{1} (Fin n) (HMod.hMod.{0 0 0} (Fin n) (Fin n) (Fin n) (instHMod.{0} (Fin n) (Fin.instModFin n)) a m) (Fin.mk n (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (Fin.val n a) (Fin.val n m)) n) (Nat.mod_lt (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (Fin.val n a) (Fin.val n m)) n (Fin.size_positive n a)))
Case conversion may be inaccurate. Consider using '#align fin.mod_def Fin.mod_defₓ'. -/
theorem mod_def (a b : Fin n) : (a % b).val = a.val % b.val :=
  show (Fin.mod a b).val = a.val % b.val by cases a <;> cases b <;> simp [Fin.mod]

theorem div_def (a b : Fin n) : (a / b).val = a.val / b.val :=
  show (Fin.div a b).val = a.val / b.val by cases a <;> cases b <;> simp [Fin.div]

theorem lt_def (a b : Fin n) : (a < b) = (a.val < b.val) :=
  show Fin.Lt a b = (a.val < b.val) by cases a <;> cases b <;> simp [Fin.Lt]

theorem le_def (a b : Fin n) : (a ≤ b) = (a.val ≤ b.val) :=
  show Fin.Le a b = (a.val ≤ b.val) by cases a <;> cases b <;> simp [Fin.Le]

theorem val_zero : (0 : Fin (succ n)).val = 0 :=
  rfl

def pred {n : Nat} : ∀ i : Fin (succ n), i ≠ 0 → Fin n
  | ⟨a, h₁⟩, h₂ =>
    ⟨a.pred,
      haveI : a ≠ 0 := by
        have aux₁ := vne_of_ne h₂
        dsimp at aux₁
        rw [val_zero] at aux₁
        exact aux₁
      Nat.pred_lt_pred this h₁⟩

end Fin

