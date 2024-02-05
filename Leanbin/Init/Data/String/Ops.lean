/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.Data.Bool.Lemmas
import Init.Data.String.Basic
import Init.Meta.WellFoundedTactics

#align_import init.data.string.ops from "leanprover-community/lean"@"9af482290ef68e8aaa5ead01aa7b09b7be7019fd"

namespace String

namespace Iterator

@[simp]
theorem nextToString_mkIterator (s : String) : s.mkIterator.nextToString = s := by
  induction s <;> rfl
#align string.iterator.next_to_string_mk_iterator String.Iterator.nextToString_mkIterator

@[simp]
theorem length_nextToString_next (it : Iterator) :
    it.next.nextToString.length = it.nextToString.length - 1 := by
  cases it <;> cases it_snd <;>
    simp [iterator.next, iterator.next_to_string, String.length, Nat.add_sub_cancel_left]
#align string.iterator.length_next_to_string_next String.Iterator.length_nextToString_next

theorem zero_lt_length_nextToString_of_hasNext {it : Iterator} :
    it.hasNext → 0 < it.nextToString.length := by
  cases it <;> cases it_snd <;>
    simp [iterator.has_next, iterator.next_to_string, String.length, Nat.zero_lt_one_add,
      Nat.add_comm, false_imp_iff]
#align string.iterator.zero_lt_length_next_to_string_of_has_next String.Iterator.zero_lt_length_nextToString_of_hasNext

end Iterator

/- ./././Mathport/Syntax/Translate/Command.lean:299:8: warning: using_well_founded used, estimated equivalent -/
-- TODO(Sebastian): generalize to something like
-- https://doc.rust-lang.org/std/primitive.str.html#method.split
private def split_core (p : Char → Bool) : Iterator → Iterator → List String
  | start, stop =>
    if h : stop.hasNext then
      -- wf hint
      have : stop.nextToString.length - 1 < stop.nextToString.length :=
        Nat.sub_lt (Iterator.zero_lt_length_nextToString_of_hasNext h) (by decide)
      if p stop.curr then
        let rest := stop.next.nextToString
        (start.extract stop).getD "" :: split_core stop.next stop.next
      else split_core start stop.next
    else [start.nextToString]
termination_by x => WellFounded.wrap (measure_wf fun e => e.2.nextToString.length) x

#print String.split /-
def split (p : Char → Bool) (s : String) : List String :=
  splitCore p s.mkIterator s.mkIterator
#align string.split String.split
-/

end String

