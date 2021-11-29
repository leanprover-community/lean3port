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
| lt => Gt
| Eq => Eq
| Gt => lt

@[inline]
def or_else : Ordering → Ordering → Ordering
| lt, _ => lt
| Eq, o => o
| Gt, _ => Gt

theorem swap_swap : ∀ o : Ordering, o.swap.swap = o
| lt => rfl
| Eq => rfl
| Gt => rfl

end Ordering

def cmpUsing {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

def cmp {α : Type u} [LT α] [DecidableRel (· < · : α → α → Prop)] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b

instance : DecidableEq Ordering :=
  fun a b =>
    match a with 
    | Ordering.lt =>
      match b with 
      | Ordering.lt => is_true rfl
      | Ordering.eq => is_false fun h => Ordering.noConfusion h
      | Ordering.gt => is_false fun h => Ordering.noConfusion h
    | Ordering.eq =>
      match b with 
      | Ordering.lt => is_false fun h => Ordering.noConfusion h
      | Ordering.eq => is_true rfl
      | Ordering.gt => is_false fun h => Ordering.noConfusion h
    | Ordering.gt =>
      match b with 
      | Ordering.lt => is_false fun h => Ordering.noConfusion h
      | Ordering.eq => is_false fun h => Ordering.noConfusion h
      | Ordering.gt => is_true rfl

