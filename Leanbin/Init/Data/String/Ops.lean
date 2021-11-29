prelude 
import Leanbin.Init.Data.Bool.Lemmas 
import Leanbin.Init.Data.String.Basic 
import Leanbin.Init.Meta.WellFoundedTactics

namespace Stringₓ

namespace Iterator

@[simp]
theorem next_to_string_mk_iterator (s : Stringₓ) : s.mk_iterator.next_to_string = s :=
  by 
    induction s <;> rfl

@[simp]
theorem length_next_to_string_next (it : iterator) : it.next.next_to_string.length = it.next_to_string.length - 1 :=
  by 
    cases it <;> cases it_snd <;> simp [iterator.next, iterator.next_to_string, Stringₓ.length, Nat.add_sub_cancel_left]

theorem zero_lt_length_next_to_string_of_has_next {it : iterator} : it.has_next → 0 < it.next_to_string.length :=
  by 
    cases it <;>
      cases it_snd <;>
        simp [iterator.has_next, iterator.next_to_string, Stringₓ.length, Nat.zero_lt_one_add, Nat.add_comm,
          false_implies_iff]

end Iterator

private def split_core (p : Charₓ → Bool) : iterator → iterator → List Stringₓ
| start, stop =>
  if h : stop.has_next then
    have  : stop.next_to_string.length - 1 < stop.next_to_string.length :=
      Nat.sub_ltₓ (iterator.zero_lt_length_next_to_string_of_has_next h)
        (by 
          decide)
    if p stop.curr then
      let rest := stop.next.next_to_string
      (start.extract stop).getOrElse "" :: split_core stop.next stop.next
    else split_core start stop.next
  else [start.next_to_string]

def split (p : Charₓ → Bool) (s : Stringₓ) : List Stringₓ :=
  split_core p s.mk_iterator s.mk_iterator

end Stringₓ

