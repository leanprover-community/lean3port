/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.ordering.basic
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Repr
import Leanbin.Init.Data.Prod
import Leanbin.Init.Data.Sum.Basic

universe u v

#print Ordering /-
inductive Ordering
  | lt
  | Eq
  | GT.gt
#align ordering Ordering
-/

instance : Repr Ordering :=
  ⟨fun s =>
    match s with
    | Ordering.lt => "lt"
    | Ordering.eq => "eq"
    | Ordering.gt => "gt"⟩

namespace Ordering

#print Ordering.swap /-
def swap : Ordering → Ordering
  | lt => gt
  | Eq => eq
  | GT.gt => lt
#align ordering.swap Ordering.swap
-/

#print Ordering.orElse /-
@[inline]
def orElse : Ordering → Ordering → Ordering
  | lt, _ => lt
  | Eq, o => o
  | GT.gt, _ => gt
#align ordering.or_else Ordering.orElse
-/

#print Ordering.swap_swap /-
theorem swap_swap : ∀ o : Ordering, o.swap.swap = o
  | lt => rfl
  | Eq => rfl
  | GT.gt => rfl
#align ordering.swap_swap Ordering.swap_swap
-/

end Ordering

#print cmpUsing /-
def cmpUsing {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq
#align cmp_using cmpUsing
-/

#print cmp /-
def cmp {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b
#align cmp cmp
-/

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

