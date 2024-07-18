/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Tuples are lists of a fixed size.
It is implemented as a subtype.
-/
prelude
import Leanbin.Init.Data.List.Default
import Leanbin.Init.Data.Subtype.Default
import Init.Meta.Interactive
import Leanbin.Init.Data.Fin.Default

#align_import data.vector from "leanprover-community/lean"@"78b8dbdf66ac8db31afa8fe3d0d7f1d0bf1be236"

universe u v w

#print Mathlib.Vector /-
def Mathlib.Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }
#align vector Mathlib.Vector
-/

namespace Mathlib.Vector

variable {α : Type u} {β : Type v} {φ : Type w}

variable {n : ℕ}

instance [DecidableEq α] : DecidableEq (Mathlib.Vector α n) := by unfold Mathlib.Vector;
  infer_instance

#print Mathlib.Vector.nil /-
@[match_pattern]
def Mathlib.Vector.nil : Mathlib.Vector α 0 :=
  ⟨[], rfl⟩
#align vector.nil Mathlib.Vector.nil
-/

#print Mathlib.Vector.cons /-
@[match_pattern]
def Mathlib.Vector.cons : α → Mathlib.Vector α n → Mathlib.Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congr_arg Nat.succ h⟩
#align vector.cons Mathlib.Vector.cons
-/

#print Mathlib.Vector.length /-
@[reducible]
def Mathlib.Vector.length (v : Mathlib.Vector α n) : ℕ :=
  n
#align vector.length Mathlib.Vector.length
-/

open Nat

#print Mathlib.Vector.head /-
def Mathlib.Vector.head : Mathlib.Vector α (Nat.succ n) → α
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: v, h⟩ => a
#align vector.head Mathlib.Vector.head
-/

#print Mathlib.Vector.head_cons /-
theorem Mathlib.Vector.head_cons (a : α) :
    ∀ v : Mathlib.Vector α n, Mathlib.Vector.head (Mathlib.Vector.cons a v) = a
  | ⟨l, h⟩ => rfl
#align vector.head_cons Mathlib.Vector.head_cons
-/

#print Mathlib.Vector.tail /-
def Mathlib.Vector.tail : Mathlib.Vector α n → Mathlib.Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congr_arg pred h⟩
  | ⟨a :: v, h⟩ => ⟨v, congr_arg pred h⟩
#align vector.tail Mathlib.Vector.tail
-/

#print Mathlib.Vector.tail_cons /-
theorem Mathlib.Vector.tail_cons (a : α) :
    ∀ v : Mathlib.Vector α n, Mathlib.Vector.tail (Mathlib.Vector.cons a v) = v
  | ⟨l, h⟩ => rfl
#align vector.tail_cons Mathlib.Vector.tail_cons
-/

#print Mathlib.Vector.cons_head_tail /-
@[simp]
theorem Mathlib.Vector.cons_head_tail :
    ∀ v : Mathlib.Vector α (succ n),
      Mathlib.Vector.cons (Mathlib.Vector.head v) (Mathlib.Vector.tail v) = v
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: v, h⟩ => rfl
#align vector.cons_head_tail Mathlib.Vector.cons_head_tail
-/

#print Mathlib.Vector.toList /-
def Mathlib.Vector.toList (v : Mathlib.Vector α n) : List α :=
  v.1
#align vector.to_list Mathlib.Vector.toList
-/

#print Mathlib.Vector.get /-
def Mathlib.Vector.get : ∀ v : Mathlib.Vector α n, Fin n → α
  | ⟨l, h⟩, i => l.nthLe i.1 (by rw [h] <;> exact i.2)
#align vector.nth Mathlib.Vector.get
-/

#print Mathlib.Vector.append /-
def Mathlib.Vector.append {n m : Nat} :
    Mathlib.Vector α n → Mathlib.Vector α m → Mathlib.Vector α (n + m)
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩
#align vector.append Mathlib.Vector.append
-/

#print Mathlib.Vector.elim /-
@[elab_as_elim]
def Mathlib.Vector.elim {α} {C : ∀ {n}, Mathlib.Vector α n → Sort u} (H : ∀ l : List α, C ⟨l, rfl⟩)
    {n : Nat} : ∀ v : Mathlib.Vector α n, C v
  | ⟨l, h⟩ =>
    match n, h with
    | _, rfl => H l
#align vector.elim Mathlib.Vector.elim
-/

#print Mathlib.Vector.map /-
-- map
def Mathlib.Vector.map (f : α → β) : Mathlib.Vector α n → Mathlib.Vector β n
  | ⟨l, h⟩ => ⟨List.map f l, by simp [*]⟩
#align vector.map Mathlib.Vector.map
-/

#print Mathlib.Vector.map_nil /-
@[simp]
theorem Mathlib.Vector.map_nil (f : α → β) :
    Mathlib.Vector.map f Mathlib.Vector.nil = Mathlib.Vector.nil :=
  rfl
#align vector.map_nil Mathlib.Vector.map_nil
-/

#print Mathlib.Vector.map_cons /-
theorem Mathlib.Vector.map_cons (f : α → β) (a : α) :
    ∀ v : Mathlib.Vector α n,
      Mathlib.Vector.map f (Mathlib.Vector.cons a v) =
        Mathlib.Vector.cons (f a) (Mathlib.Vector.map f v)
  | ⟨l, h⟩ => rfl
#align vector.map_cons Mathlib.Vector.map_cons
-/

#print Mathlib.Vector.map₂ /-
def Mathlib.Vector.map₂ (f : α → β → φ) :
    Mathlib.Vector α n → Mathlib.Vector β n → Mathlib.Vector φ n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.zipWith f x y, by simp [*]⟩
#align vector.map₂ Mathlib.Vector.map₂
-/

def Mathlib.Vector.repeat (a : α) (n : ℕ) : Mathlib.Vector α n :=
  ⟨List.repeat a n, List.length_replicate a n⟩
#align vector.repeat Mathlib.Vector.repeat

#print Mathlib.Vector.drop /-
def Mathlib.Vector.drop (i : ℕ) : Mathlib.Vector α n → Mathlib.Vector α (n - i)
  | ⟨l, p⟩ => ⟨List.drop i l, by simp [*]⟩
#align vector.drop Mathlib.Vector.drop
-/

#print Mathlib.Vector.take /-
def Mathlib.Vector.take (i : ℕ) : Mathlib.Vector α n → Mathlib.Vector α (min i n)
  | ⟨l, p⟩ => ⟨List.take i l, by simp [*]⟩
#align vector.take Mathlib.Vector.take
-/

#print Mathlib.Vector.eraseIdx /-
def Mathlib.Vector.eraseIdx (i : Fin n) : Mathlib.Vector α n → Mathlib.Vector α (n - 1)
  | ⟨l, p⟩ => ⟨List.eraseIdx l i.1, by rw [l.length_remove_nth i.1] <;> rw [p] <;> exact i.2⟩
#align vector.remove_nth Mathlib.Vector.eraseIdx
-/

#print Mathlib.Vector.ofFn /-
def Mathlib.Vector.ofFn : ∀ {n}, (Fin n → α) → Mathlib.Vector α n
  | 0, f => Mathlib.Vector.nil
  | n + 1, f => Mathlib.Vector.cons (f 0) (of_fn fun i => f i.succ)
#align vector.of_fn Mathlib.Vector.ofFn
-/

section Accum

open Prod

variable {σ : Type}

#print Mathlib.Vector.mapAccumr /-
def Mathlib.Vector.mapAccumr (f : α → σ → σ × β) : Mathlib.Vector α n → σ → σ × Mathlib.Vector β n
  | ⟨x, px⟩, c =>
    let res := List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*]⟩
#align vector.map_accumr Mathlib.Vector.mapAccumr
-/

#print Mathlib.Vector.mapAccumr₂ /-
def Mathlib.Vector.mapAccumr₂ {α β σ φ : Type} (f : α → β → σ → σ × φ) :
    Mathlib.Vector α n → Mathlib.Vector β n → σ → σ × Mathlib.Vector φ n
  | ⟨x, px⟩, ⟨y, py⟩, c =>
    let res := List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*]⟩
#align vector.map_accumr₂ Mathlib.Vector.mapAccumr₂
-/

end Accum

#print Mathlib.Vector.eq /-
protected theorem Mathlib.Vector.eq {n : ℕ} :
    ∀ a1 a2 : Mathlib.Vector α n, Mathlib.Vector.toList a1 = Mathlib.Vector.toList a2 → a1 = a2
  | ⟨x, h1⟩, ⟨_, h2⟩, rfl => rfl
#align vector.eq Mathlib.Vector.eq
-/

#print Mathlib.Vector.eq_nil /-
protected theorem Mathlib.Vector.eq_nil (v : Mathlib.Vector α 0) : v = Mathlib.Vector.nil :=
  v.Eq Mathlib.Vector.nil (List.eq_nil_of_length_eq_zero v.2)
#align vector.eq_nil Mathlib.Vector.eq_nil
-/

#print Mathlib.Vector.toList_mk /-
@[simp]
theorem Mathlib.Vector.toList_mk (v : List α) (P : List.length v = n) :
    Mathlib.Vector.toList (Subtype.mk v P) = v :=
  rfl
#align vector.to_list_mk Mathlib.Vector.toList_mk
-/

#print Mathlib.Vector.toList_nil /-
@[simp]
theorem Mathlib.Vector.toList_nil : Mathlib.Vector.toList Mathlib.Vector.nil = @List.nil α :=
  rfl
#align vector.to_list_nil Mathlib.Vector.toList_nil
-/

#print Mathlib.Vector.toList_length /-
@[simp]
theorem Mathlib.Vector.toList_length (v : Mathlib.Vector α n) :
    (Mathlib.Vector.toList v).length = n :=
  v.2
#align vector.to_list_length Mathlib.Vector.toList_length
-/

#print Mathlib.Vector.toList_cons /-
@[simp]
theorem Mathlib.Vector.toList_cons (a : α) (v : Mathlib.Vector α n) :
    Mathlib.Vector.toList (Mathlib.Vector.cons a v) = a :: Mathlib.Vector.toList v := by cases v;
  rfl
#align vector.to_list_cons Mathlib.Vector.toList_cons
-/

#print Mathlib.Vector.toList_append /-
@[simp]
theorem Mathlib.Vector.toList_append {n m : Nat} (v : Mathlib.Vector α n) (w : Mathlib.Vector α m) :
    Mathlib.Vector.toList (Mathlib.Vector.append v w) =
      Mathlib.Vector.toList v ++ Mathlib.Vector.toList w :=
  by cases v; cases w; rfl
#align vector.to_list_append Mathlib.Vector.toList_append
-/

#print Mathlib.Vector.toList_drop /-
@[simp]
theorem Mathlib.Vector.toList_drop {n m : ℕ} (v : Mathlib.Vector α m) :
    Mathlib.Vector.toList (Mathlib.Vector.drop n v) = List.drop n (Mathlib.Vector.toList v) := by
  cases v; rfl
#align vector.to_list_drop Mathlib.Vector.toList_drop
-/

#print Mathlib.Vector.toList_take /-
@[simp]
theorem Mathlib.Vector.toList_take {n m : ℕ} (v : Mathlib.Vector α m) :
    Mathlib.Vector.toList (Mathlib.Vector.take n v) = List.take n (Mathlib.Vector.toList v) := by
  cases v; rfl
#align vector.to_list_take Mathlib.Vector.toList_take
-/

end Mathlib.Vector

