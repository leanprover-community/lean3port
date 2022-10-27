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
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Data.Fin.Default

universe u v w

def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }

namespace Vector

variable {α : Type u} {β : Type v} {φ : Type w}

variable {n : ℕ}

instance [DecidableEq α] : DecidableEq (Vector α n) := by
  unfold Vector
  infer_instance

@[match_pattern]
def nil : Vector α 0 :=
  ⟨[], rfl⟩

@[match_pattern]
def cons : α → Vector α n → Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congr_arg Nat.succ h⟩

@[reducible]
def length (v : Vector α n) : ℕ :=
  n

open Nat

def head : Vector α (Nat.succ n) → α
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: v, h⟩ => a

theorem head_cons (a : α) : ∀ v : Vector α n, head (cons a v) = a
  | ⟨l, h⟩ => rfl

def tail : Vector α n → Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congr_arg pred h⟩
  | ⟨a :: v, h⟩ => ⟨v, congr_arg pred h⟩

theorem tail_cons (a : α) : ∀ v : Vector α n, tail (cons a v) = v
  | ⟨l, h⟩ => rfl

@[simp]
theorem cons_head_tail : ∀ v : Vector α (succ n), cons (head v) (tail v) = v
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: v, h⟩ => rfl

def toList (v : Vector α n) : List α :=
  v.1

def nth : ∀ v : Vector α n, Fin n → α
  | ⟨l, h⟩, i => l.nthLe i.1 (by rw [h] <;> exact i.2)

def append {n m : Nat} : Vector α n → Vector α m → Vector α (n + m)
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩

/- warning: vector.elim -> Vector.elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {C : forall {n : Nat}, (Vector.{u_1} α n) -> Sort.{u}}, (forall (l : List.{u_1} α), C (List.length.{u_1} α l) (Subtype.mk.{succ u_1} (List.{u_1} α) (fun (l_1 : List.{u_1} α) => Eq.{1} Nat (List.length.{u_1} α l_1) (List.length.{u_1} α l)) l (Vector.Elim._proof_1.{u_1} α l))) -> (forall {n : Nat} (v : Vector.{u_1} α n), C n v)
but is expected to have type
  forall {α : Type.{_aux_param_0}} {C : forall {n : Nat}, (Vector.{_aux_param_0} α n) -> Sort.{u}}, (forall (l : List.{_aux_param_0} α), C (List.length.{_aux_param_0} α l) (Subtype.mk.{succ _aux_param_0} (List.{_aux_param_0} α) (fun (l_1 : List.{_aux_param_0} α) => Eq.{1} Nat (List.length.{_aux_param_0} α l_1) (List.length.{_aux_param_0} α l)) l (rfl.{1} Nat (List.length.{_aux_param_0} α l)))) -> (forall {n : Nat} (v : Vector.{_aux_param_0} α n), C n v)
Case conversion may be inaccurate. Consider using '#align vector.elim Vector.elimₓ'. -/
@[elab_as_elim]
def elim {α} {C : ∀ {n}, Vector α n → Sort u} (H : ∀ l : List α, C ⟨l, rfl⟩) {n : Nat} : ∀ v : Vector α n, C v
  | ⟨l, h⟩ =>
    match n, h with
    | _, rfl => H l

-- map
def map (f : α → β) : Vector α n → Vector β n
  | ⟨l, h⟩ => ⟨List.map f l, by simp [*]⟩

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl

theorem map_cons (f : α → β) (a : α) : ∀ v : Vector α n, map f (cons a v) = cons (f a) (map f v)
  | ⟨l, h⟩ => rfl

def map₂ (f : α → β → φ) : Vector α n → Vector β n → Vector φ n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.map₂ f x y, by simp [*]⟩

def repeat (a : α) (n : ℕ) : Vector α n :=
  ⟨List.repeat a n, List.length_repeat a n⟩

def drop (i : ℕ) : Vector α n → Vector α (n - i)
  | ⟨l, p⟩ => ⟨List.drop i l, by simp [*]⟩

def take (i : ℕ) : Vector α n → Vector α (min i n)
  | ⟨l, p⟩ => ⟨List.take i l, by simp [*]⟩

def removeNth (i : Fin n) : Vector α n → Vector α (n - 1)
  | ⟨l, p⟩ => ⟨List.removeNth l i.1, by rw [l.length_remove_nth i.1] <;> rw [p] <;> exact i.2⟩

def ofFn : ∀ {n}, (Fin n → α) → Vector α n
  | 0, f => nil
  | n + 1, f => cons (f 0) (of_fn fun i => f i.succ)

section Accum

open Prod

variable {σ : Type}

def mapAccumr (f : α → σ → σ × β) : Vector α n → σ → σ × Vector β n
  | ⟨x, px⟩, c =>
    let res := List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*]⟩

def mapAccumr₂ {α β σ φ : Type} (f : α → β → σ → σ × φ) : Vector α n → Vector β n → σ → σ × Vector φ n
  | ⟨x, px⟩, ⟨y, py⟩, c =>
    let res := List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*]⟩

end Accum

protected theorem eq {n : ℕ} : ∀ a1 a2 : Vector α n, toList a1 = toList a2 → a1 = a2
  | ⟨x, h1⟩, ⟨_, h2⟩, rfl => rfl

protected theorem eq_nil (v : Vector α 0) : v = nil :=
  v.Eq nil (List.eq_nil_of_length_eq_zero v.2)

@[simp]
theorem to_list_mk (v : List α) (P : List.length v = n) : toList (Subtype.mk v P) = v :=
  rfl

@[simp]
theorem to_list_nil : toList nil = @List.nil α :=
  rfl

@[simp]
theorem to_list_length (v : Vector α n) : (toList v).length = n :=
  v.2

@[simp]
theorem to_list_cons (a : α) (v : Vector α n) : toList (cons a v) = a :: toList v := by
  cases v
  rfl

@[simp]
theorem to_list_append {n m : Nat} (v : Vector α n) (w : Vector α m) : toList (append v w) = toList v ++ toList w := by
  cases v
  cases w
  rfl

@[simp]
theorem to_list_drop {n m : ℕ} (v : Vector α m) : toList (drop n v) = List.drop n (toList v) := by
  cases v
  rfl

@[simp]
theorem to_list_take {n m : ℕ} (v : Vector α m) : toList (take n v) = List.take n (toList v) := by
  cases v
  rfl

end Vector

