/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Leanbin.Init.Data.Bool.Lemmas
import Leanbin.Init.Data.String.Basic
import Leanbin.Init.Meta.WellFoundedTactics

namespace Stringₓ

namespace Iterator

@[simp]
theorem next_to_string_mk_iterator (s : Stringₓ) : s.mkIterator.nextToString = s := by
  induction s <;> rfl

@[simp]
theorem length_next_to_string_next (it : Iterator) : it.next.nextToString.length = it.nextToString.length - 1 := by
  cases it <;>
    cases it_snd <;> simp [← iterator.next, ← iterator.next_to_string, ← Stringₓ.length, ← Nat.add_sub_cancel_left]

theorem zero_lt_length_next_to_string_of_has_next {it : Iterator} : it.hasNext → 0 < it.nextToString.length := by
  cases it <;>
    cases it_snd <;>
      simp [← iterator.has_next, ← iterator.next_to_string, ← Stringₓ.length, ← Nat.zero_lt_one_add, ← Nat.add_comm, ←
        false_implies_iff]

end Iterator

-- TODO(Sebastian): generalize to something like
-- https://doc.rust-lang.org/std/primitive.str.html#method.split
private def split_core (p : Charₓ → Bool) : Iterator → Iterator → List Stringₓ
  | start, stop =>
    if h : stop.hasNext then
      -- wf hint
      have : stop.nextToString.length - 1 < stop.nextToString.length :=
        Nat.sub_ltₓ (Iterator.zero_lt_length_next_to_string_of_has_next h)
          (by
            decide)
      if p stop.curr then
        let rest := stop.next.nextToString
        (start.extract stop).getOrElse "" :: split_core stop.next stop.next
      else split_core start stop.next
    else [start.nextToString]

def split (p : Charₓ → Bool) (s : Stringₓ) : List Stringₓ :=
  splitCore p s.mkIterator s.mkIterator

end Stringₓ

