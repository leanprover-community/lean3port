/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Repr
import Leanbin.Init.Data.Prod
import Leanbin.Init.Data.Sum.Basic

universe u v

inductive Ordering
  | lt
  | Eq
  | Gt

instance : HasRepr Ordering :=
  ⟨fun s =>
    match s with
    | Ordering.lt => "lt"
    | Ordering.eq => "eq"
    | Ordering.gt => "gt"⟩

namespace Ordering

def swap : Ordering → Ordering
  | lt => gt
  | Eq => eq
  | Gt => lt

@[inline]
def orElse : Ordering → Ordering → Ordering
  | lt, _ => lt
  | Eq, o => o
  | Gt, _ => gt

theorem swap_swap : ∀ o : Ordering, o.swap.swap = o
  | lt => rfl
  | Eq => rfl
  | Gt => rfl

end Ordering

def cmpUsing {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

def cmp {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b

instance : DecidableEq Ordering := fun a b =>
  match a with
  | Ordering.lt =>
    match b with
    | Ordering.lt => isTrue rfl
    | Ordering.eq => isFalse fun h => Ordering.noConfusion h
    | Ordering.gt => isFalse fun h => Ordering.noConfusion h
  | Ordering.eq =>
    match b with
    | Ordering.lt => isFalse fun h => Ordering.noConfusion h
    | Ordering.eq => isTrue rfl
    | Ordering.gt => isFalse fun h => Ordering.noConfusion h
  | Ordering.gt =>
    match b with
    | Ordering.lt => isFalse fun h => Ordering.noConfusion h
    | Ordering.eq => isFalse fun h => Ordering.noConfusion h
    | Ordering.gt => isTrue rfl

