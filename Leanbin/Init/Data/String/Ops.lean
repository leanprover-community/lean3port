/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Leanbin.Init.Data.Bool.Lemmas
import Leanbin.Init.Data.String.Basic
import Leanbin.Init.Meta.WellFoundedTactics

namespace String

namespace Iterator

@[simp]
theorem next_to_string_mk_iterator (s : String) : s.mkIterator.nextToString = s := by induction s <;> rfl

@[simp]
theorem length_next_to_string_next (it : Iterator) : it.next.nextToString.length = it.nextToString.length - 1 := by
  cases it <;> cases it_snd <;> simp [iterator.next, iterator.next_to_string, String.length, Nat.add_sub_cancel_left]

theorem zero_lt_length_next_to_string_of_has_next {it : Iterator} : it.hasNext → 0 < it.nextToString.length := by
  cases it <;>
    cases it_snd <;>
      simp [iterator.has_next, iterator.next_to_string, String.length, Nat.zero_lt_one_add, Nat.add_comm, false_imp_iff]

end Iterator

-- TODO(Sebastian): generalize to something like
-- https://doc.rust-lang.org/std/primitive.str.html#method.split
private def split_core (p : Char → Bool) : Iterator → Iterator → List String
  | start, stop =>
    if h : stop.hasNext then
      -- wf hint
      have : stop.nextToString.length - 1 < stop.nextToString.length :=
        Nat.sub_lt (Iterator.zero_lt_length_next_to_string_of_has_next h) (by decide)
      if p stop.curr then
        let rest := stop.next.nextToString
        (start.extract stop).getOrElse "" :: split_core stop.next stop.next
      else split_core start stop.next
    else [start.nextToString]

/- warning: string.split -> String.split is a dubious translation:
lean 3 declaration is
  (Char -> Bool) -> String -> (List.{0} String)
but is expected to have type
  String -> (Char -> Bool) -> (List.{0} String)
Case conversion may be inaccurate. Consider using '#align string.split String.splitₓ'. -/
def split (p : Char → Bool) (s : String) : List String :=
  splitCore p s.mkIterator s.mkIterator

end String

