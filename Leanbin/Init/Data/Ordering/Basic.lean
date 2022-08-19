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

namespace Ordering

def swap : Ordering → Ordering
  | lt => gt
  | eq => eq
  | gt => lt

@[inline]
def orElse : Ordering → Ordering → Ordering
  | lt, _ => lt
  | eq, o => o
  | gt, _ => gt

theorem swap_swap : ∀ o : Ordering, o.swap.swap = o
  | lt => rfl
  | eq => rfl
  | gt => rfl

end Ordering

def cmpUsing {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

def cmp {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b

deriving instance DecidableEq for Ordering

