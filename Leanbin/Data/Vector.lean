/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Tuples are lists of a fixed size.
It is implemented as a subtype.

! This file was ported from Lean 3 source module data.vector
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.List.Default
import Leanbin.Init.Data.Subtype.Default
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Data.Fin.Default

universe u v w

#print Vector /-
def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }
#align vector Vector
-/

namespace Vector

variable {α : Type u} {β : Type v} {φ : Type w}

variable {n : ℕ}

instance [DecidableEq α] : DecidableEq (Vector α n) := by unfold Vector; infer_instance

#print Vector.nil /-
@[match_pattern]
def nil : Vector α 0 :=
  ⟨[], rfl⟩
#align vector.nil Vector.nil
-/

#print Vector.cons /-
@[match_pattern]
def cons : α → Vector α n → Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congr_arg Nat.succ h⟩
#align vector.cons Vector.cons
-/

#print Vector.length /-
@[reducible]
def length (v : Vector α n) : ℕ :=
  n
#align vector.length Vector.length
-/

open Nat

#print Vector.head /-
def head : Vector α (Nat.succ n) → α
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: v, h⟩ => a
#align vector.head Vector.head
-/

#print Vector.head_cons /-
theorem head_cons (a : α) : ∀ v : Vector α n, head (cons a v) = a
  | ⟨l, h⟩ => rfl
#align vector.head_cons Vector.head_cons
-/

#print Vector.tail /-
def tail : Vector α n → Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congr_arg pred h⟩
  | ⟨a :: v, h⟩ => ⟨v, congr_arg pred h⟩
#align vector.tail Vector.tail
-/

#print Vector.tail_cons /-
theorem tail_cons (a : α) : ∀ v : Vector α n, tail (cons a v) = v
  | ⟨l, h⟩ => rfl
#align vector.tail_cons Vector.tail_cons
-/

#print Vector.cons_head_tail /-
@[simp]
theorem cons_head_tail : ∀ v : Vector α (succ n), cons (head v) (tail v) = v
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: v, h⟩ => rfl
#align vector.cons_head_tail Vector.cons_head_tail
-/

#print Vector.toList /-
def toList (v : Vector α n) : List α :=
  v.1
#align vector.to_list Vector.toList
-/

#print Vector.get /-
def get : ∀ v : Vector α n, Fin n → α
  | ⟨l, h⟩, i => l.nthLe i.1 (by rw [h] <;> exact i.2)
#align vector.nth Vector.get
-/

#print Vector.append /-
def append {n m : Nat} : Vector α n → Vector α m → Vector α (n + m)
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩
#align vector.append Vector.append
-/

#print Vector.elim /-
@[elab_as_elim]
def elim {α} {C : ∀ {n}, Vector α n → Sort u} (H : ∀ l : List α, C ⟨l, rfl⟩) {n : Nat} :
    ∀ v : Vector α n, C v
  | ⟨l, h⟩ =>
    match n, h with
    | _, rfl => H l
#align vector.elim Vector.elim
-/

#print Vector.map /-
-- map
def map (f : α → β) : Vector α n → Vector β n
  | ⟨l, h⟩ => ⟨List.map f l, by simp [*]⟩
#align vector.map Vector.map
-/

#print Vector.map_nil /-
@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
#align vector.map_nil Vector.map_nil
-/

#print Vector.map_cons /-
theorem map_cons (f : α → β) (a : α) : ∀ v : Vector α n, map f (cons a v) = cons (f a) (map f v)
  | ⟨l, h⟩ => rfl
#align vector.map_cons Vector.map_cons
-/

#print Vector.map₂ /-
def map₂ (f : α → β → φ) : Vector α n → Vector β n → Vector φ n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.zipWith f x y, by simp [*]⟩
#align vector.map₂ Vector.map₂
-/

def repeat (a : α) (n : ℕ) : Vector α n :=
  ⟨List.repeat a n, List.length_repeat a n⟩
#align vector.repeat Vector.repeat

#print Vector.drop /-
def drop (i : ℕ) : Vector α n → Vector α (n - i)
  | ⟨l, p⟩ => ⟨List.drop i l, by simp [*]⟩
#align vector.drop Vector.drop
-/

/- warning: vector.take -> Vector.take is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} (i : Nat), (Vector.{u1} α n) -> (Vector.{u1} α (LinearOrder.min.{0} Nat Nat.linearOrder i n))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} (i : Nat), (Vector.{u1} α n) -> (Vector.{u1} α (Min.min.{0} Nat Nat.instMinNat i n))
Case conversion may be inaccurate. Consider using '#align vector.take Vector.takeₓ'. -/
def take (i : ℕ) : Vector α n → Vector α (min i n)
  | ⟨l, p⟩ => ⟨List.take i l, by simp [*]⟩
#align vector.take Vector.take

#print Vector.removeNth /-
def removeNth (i : Fin n) : Vector α n → Vector α (n - 1)
  | ⟨l, p⟩ => ⟨List.removeNth l i.1, by rw [l.length_remove_nth i.1] <;> rw [p] <;> exact i.2⟩
#align vector.remove_nth Vector.removeNth
-/

#print Vector.ofFn /-
def ofFn : ∀ {n}, (Fin n → α) → Vector α n
  | 0, f => nil
  | n + 1, f => cons (f 0) (of_fn fun i => f i.succ)
#align vector.of_fn Vector.ofFn
-/

section Accum

open Prod

variable {σ : Type}

#print Vector.mapAccumr /-
def mapAccumr (f : α → σ → σ × β) : Vector α n → σ → σ × Vector β n
  | ⟨x, px⟩, c =>
    let res := List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*]⟩
#align vector.map_accumr Vector.mapAccumr
-/

#print Vector.mapAccumr₂ /-
def mapAccumr₂ {α β σ φ : Type} (f : α → β → σ → σ × φ) :
    Vector α n → Vector β n → σ → σ × Vector φ n
  | ⟨x, px⟩, ⟨y, py⟩, c =>
    let res := List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*]⟩
#align vector.map_accumr₂ Vector.mapAccumr₂
-/

end Accum

#print Vector.eq /-
protected theorem eq {n : ℕ} : ∀ a1 a2 : Vector α n, toList a1 = toList a2 → a1 = a2
  | ⟨x, h1⟩, ⟨_, h2⟩, rfl => rfl
#align vector.eq Vector.eq
-/

#print Vector.eq_nil /-
protected theorem eq_nil (v : Vector α 0) : v = nil :=
  v.Eq nil (List.eq_nil_of_length_eq_zero v.2)
#align vector.eq_nil Vector.eq_nil
-/

#print Vector.toList_mk /-
@[simp]
theorem toList_mk (v : List α) (P : List.length v = n) : toList (Subtype.mk v P) = v :=
  rfl
#align vector.to_list_mk Vector.toList_mk
-/

#print Vector.toList_nil /-
@[simp]
theorem toList_nil : toList nil = @List.nil α :=
  rfl
#align vector.to_list_nil Vector.toList_nil
-/

#print Vector.toList_length /-
@[simp]
theorem toList_length (v : Vector α n) : (toList v).length = n :=
  v.2
#align vector.to_list_length Vector.toList_length
-/

#print Vector.toList_cons /-
@[simp]
theorem toList_cons (a : α) (v : Vector α n) : toList (cons a v) = a :: toList v := by cases v; rfl
#align vector.to_list_cons Vector.toList_cons
-/

#print Vector.toList_append /-
@[simp]
theorem toList_append {n m : Nat} (v : Vector α n) (w : Vector α m) :
    toList (append v w) = toList v ++ toList w := by cases v; cases w; rfl
#align vector.to_list_append Vector.toList_append
-/

#print Vector.toList_drop /-
@[simp]
theorem toList_drop {n m : ℕ} (v : Vector α m) : toList (drop n v) = List.drop n (toList v) := by
  cases v; rfl
#align vector.to_list_drop Vector.toList_drop
-/

#print Vector.toList_take /-
@[simp]
theorem toList_take {n m : ℕ} (v : Vector α m) : toList (take n v) = List.take n (toList v) := by
  cases v; rfl
#align vector.to_list_take Vector.toList_take
-/

end Vector

