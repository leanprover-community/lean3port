/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic

namespace Nat

#print Nat.le /-
inductive le (a : ℕ) : ℕ → Prop
  | refl : less_than_or_equal a
  | step : ∀ {b}, less_than_or_equal b → less_than_or_equal (succ b)
#align nat.less_than_or_equal Nat.le
-/

instance : LE ℕ :=
  ⟨Nat.le⟩

/- warning: nat.le clashes with nat.less_than_or_equal -> Nat.le
Case conversion may be inaccurate. Consider using '#align nat.le Nat.leₓ'. -/
#print Nat.le /-
@[reducible]
protected def le (n m : ℕ) :=
  Nat.le n m
#align nat.le Nat.le
-/

#print Nat.lt /-
@[reducible]
protected def lt (n m : ℕ) :=
  Nat.le (succ n) m
#align nat.lt Nat.lt
-/

instance : LT ℕ :=
  ⟨Nat.lt⟩

#print Nat.pred /-
def pred : ℕ → ℕ
  | 0 => 0
  | a + 1 => a
#align nat.pred Nat.pred
-/

#print Nat.sub /-
protected def sub : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, b + 1 => pred (sub a b)
#align nat.sub Nat.sub
-/

#print Nat.mul /-
protected def mul : Nat → Nat → Nat
  | a, 0 => 0
  | a, b + 1 => mul a b + a
#align nat.mul Nat.mul
-/

instance : Sub ℕ :=
  ⟨Nat.sub⟩

instance : Mul ℕ :=
  ⟨Nat.mul⟩

-- defeq to the instance provided by comm_semiring
instance : Dvd ℕ :=
  Dvd.mk fun a b => ∃ c, b = a * c

instance : DecidableEq ℕ
  | zero, zero => isTrue rfl
  | succ x, zero => isFalse fun h => Nat.noConfusion h
  | zero, succ y => isFalse fun h => Nat.noConfusion h
  | succ x, succ y =>
    match DecidableEq x y with
    | is_true xeqy => isTrue (xeqy ▸ Eq.refl (succ x))
    | is_false xney => isFalse fun h => Nat.noConfusion h fun xeqy => absurd xeqy xney

def repeat'.{u} {α : Type u} (f : ℕ → α → α) : ℕ → α → α
  | 0, a => a
  | succ n, a => f n (repeat n a)
#align nat.repeat Nat.repeat'

instance : Inhabited ℕ :=
  ⟨Nat.zero⟩

#print Nat.zero_eq /-
@[simp]
theorem zero_eq : Nat.zero = 0 :=
  rfl
#align nat.nat_zero_eq_zero Nat.zero_eq
-/

/-! properties of inequality -/


#print Nat.le_refl /-
@[refl]
protected theorem le_refl (a : ℕ) : a ≤ a :=
  less_than_or_equal.refl
#align nat.le_refl Nat.le_refl
-/

#print Nat.le_succ /-
theorem le_succ (n : ℕ) : n ≤ succ n :=
  le.step (Nat.le_refl n)
#align nat.le_succ Nat.le_succ
-/

#print Nat.succ_le_succ /-
theorem succ_le_succ {n m : ℕ} : n ≤ m → succ n ≤ succ m := fun h =>
  le.ndrec (Nat.le_refl (succ n)) (fun a b => le.step) h
#align nat.succ_le_succ Nat.succ_le_succ
-/

#print Nat.zero_le /-
protected theorem zero_le : ∀ n : ℕ, 0 ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => le.step (zero_le n)
#align nat.zero_le Nat.zero_le
-/

#print Nat.zero_lt_succ /-
theorem zero_lt_succ (n : ℕ) : 0 < succ n :=
  succ_le_succ n.zero_le
#align nat.zero_lt_succ Nat.zero_lt_succ
-/

#print Nat.succ_pos /-
theorem succ_pos (n : ℕ) : 0 < succ n :=
  zero_lt_succ n
#align nat.succ_pos Nat.succ_pos
-/

#print Nat.not_succ_le_zero /-
theorem not_succ_le_zero : ∀ n : ℕ, succ n ≤ 0 → False :=
  fun.
#align nat.not_succ_le_zero Nat.not_succ_le_zero
-/

#print Nat.not_lt_zero /-
protected theorem not_lt_zero (a : ℕ) : ¬a < 0 :=
  not_succ_le_zero a
#align nat.not_lt_zero Nat.not_lt_zero
-/

#print Nat.pred_le_pred /-
theorem pred_le_pred {n m : ℕ} : n ≤ m → pred n ≤ pred m := fun h =>
  le.rec_on h (Nat.le_refl (pred n)) fun n => Nat.rec (fun a b => b) (fun a b c => le.step) n
#align nat.pred_le_pred Nat.pred_le_pred
-/

#print Nat.le_of_succ_le_succ /-
theorem le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
  pred_le_pred
#align nat.le_of_succ_le_succ Nat.le_of_succ_le_succ
-/

instance decidableLe : ∀ a b : ℕ, Decidable (a ≤ b)
  | 0, b => isTrue b.zero_le
  | a + 1, 0 => isFalse (not_succ_le_zero a)
  | a + 1, b + 1 =>
    match decidable_le a b with
    | is_true h => isTrue (succ_le_succ h)
    | is_false h => isFalse fun a => h (le_of_succ_le_succ a)
#align nat.decidable_le Nat.decidableLe

instance decidableLt : ∀ a b : ℕ, Decidable (a < b) := fun a b => Nat.decidableLe (succ a) b
#align nat.decidable_lt Nat.decidableLt

#print Nat.eq_or_lt_of_le /-
protected theorem eq_or_lt_of_le {a b : ℕ} (h : a ≤ b) : a = b ∨ a < b :=
  le.cases_on h (Or.inl rfl) fun n h => Or.inr (succ_le_succ h)
#align nat.eq_or_lt_of_le Nat.eq_or_lt_of_le
-/

#print Nat.lt_succ_of_le /-
theorem lt_succ_of_le {a b : ℕ} : a ≤ b → a < succ b :=
  succ_le_succ
#align nat.lt_succ_of_le Nat.lt_succ_of_le
-/

#print Nat.succ_sub_succ_eq_sub /-
@[simp]
theorem succ_sub_succ_eq_sub (a b : ℕ) : succ a - succ b = a - b :=
  Nat.recOn b (show succ a - succ zero = a - zero from Eq.refl (succ a - succ zero)) fun b => congr_arg pred
#align nat.succ_sub_succ_eq_sub Nat.succ_sub_succ_eq_sub
-/

#print Nat.not_succ_le_self /-
theorem not_succ_le_self : ∀ n : ℕ, ¬succ n ≤ n := fun n =>
  Nat.rec (not_succ_le_zero 0) (fun a b c => b (le_of_succ_le_succ c)) n
#align nat.not_succ_le_self Nat.not_succ_le_self
-/

#print Nat.lt_irrefl /-
protected theorem lt_irrefl (n : ℕ) : ¬n < n :=
  not_succ_le_self n
#align nat.lt_irrefl Nat.lt_irrefl
-/

#print Nat.le_trans /-
protected theorem le_trans {n m k : ℕ} (h1 : n ≤ m) : m ≤ k → n ≤ k :=
  le.ndrec h1 fun p h2 => le.step
#align nat.le_trans Nat.le_trans
-/

#print Nat.pred_le /-
theorem pred_le : ∀ n : ℕ, pred n ≤ n
  | 0 => le.refl
  | succ a => le.step le.refl
#align nat.pred_le Nat.pred_le
-/

#print Nat.pred_lt /-
theorem pred_lt : ∀ {n : ℕ}, n ≠ 0 → pred n < n
  | 0, h => absurd rfl h
  | succ a, h => lt_succ_of_le le.refl
#align nat.pred_lt Nat.pred_lt
-/

#print Nat.sub_le /-
protected theorem sub_le (a b : ℕ) : a - b ≤ a :=
  Nat.recOn b (Nat.le_refl (a - 0)) fun b₁ => Nat.le_trans (pred_le (a - b₁))
#align nat.sub_le Nat.sub_le
-/

#print Nat.sub_lt /-
protected theorem sub_lt : ∀ {a b : ℕ}, 0 < a → 0 < b → a - b < a
  | 0, b, h1, h2 => absurd h1 (Nat.lt_irrefl 0)
  | a + 1, 0, h1, h2 => absurd h2 (Nat.lt_irrefl 0)
  | a + 1, b + 1, h1, h2 => Eq.symm (succ_sub_succ_eq_sub a b) ▸ show a - b < succ a from lt_succ_of_le (a.sub_le b)
#align nat.sub_lt Nat.sub_lt
-/

#print Nat.lt_of_lt_of_le /-
protected theorem lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k :=
  Nat.le_trans
#align nat.lt_of_lt_of_le Nat.lt_of_lt_of_le
-/

/-! Basic nat.add lemmas -/


#print Nat.zero_add /-
protected theorem zero_add : ∀ n : ℕ, 0 + n = n
  | 0 => rfl
  | n + 1 => congr_arg succ (zero_add n)
#align nat.zero_add Nat.zero_add
-/

#print Nat.succ_add /-
theorem succ_add : ∀ n m : ℕ, succ n + m = succ (n + m)
  | n, 0 => rfl
  | n, m + 1 => congr_arg succ (succ_add n m)
#align nat.succ_add Nat.succ_add
-/

#print Nat.add_succ /-
theorem add_succ (n m : ℕ) : n + succ m = succ (n + m) :=
  rfl
#align nat.add_succ Nat.add_succ
-/

/- warning: nat.add_zero clashes with nat_add_zero -> Nat.add_zero
Case conversion may be inaccurate. Consider using '#align nat.add_zero Nat.add_zeroₓ'. -/
#print Nat.add_zero /-
protected theorem add_zero (n : ℕ) : n + 0 = n :=
  rfl
#align nat.add_zero Nat.add_zero
-/

#print Nat.add_one /-
theorem add_one (n : ℕ) : n + 1 = succ n :=
  rfl
#align nat.add_one Nat.add_one
-/

#print Nat.succ_eq_add_one /-
theorem succ_eq_add_one (n : ℕ) : succ n = n + 1 :=
  rfl
#align nat.succ_eq_add_one Nat.succ_eq_add_one
-/

/-! Basic lemmas for comparing numerals -/


protected theorem bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
  show succ (succ n + n) = succ (succ (n + n)) from congr_arg succ (succ_add n n)
#align nat.bit0_succ_eq Nat.bit0_succ_eq

protected theorem zero_lt_bit0 : ∀ {n : Nat}, n ≠ 0 → 0 < bit0 n
  | 0, h => absurd rfl h
  | succ n, h =>
    calc
      0 < succ (succ (bit0 n)) := zero_lt_succ _
      _ = bit0 (succ n) := (Nat.bit0_succ_eq n).symm
      
#align nat.zero_lt_bit0 Nat.zero_lt_bit0

protected theorem zero_lt_bit1 (n : Nat) : 0 < bit1 n :=
  zero_lt_succ _
#align nat.zero_lt_bit1 Nat.zero_lt_bit1

protected theorem bit0_ne_zero : ∀ {n : ℕ}, n ≠ 0 → bit0 n ≠ 0
  | 0, h => absurd rfl h
  | n + 1, h =>
    suffices n + 1 + (n + 1) ≠ 0 from this
    suffices succ (n + 1 + n) ≠ 0 from this
    fun h => Nat.noConfusion h
#align nat.bit0_ne_zero Nat.bit0_ne_zero

protected theorem bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
  show succ (n + n) ≠ 0 from fun h => Nat.noConfusion h
#align nat.bit1_ne_zero Nat.bit1_ne_zero

end Nat

