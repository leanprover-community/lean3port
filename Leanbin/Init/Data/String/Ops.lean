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
theorem next_to_string_mk_iterator (s : String) : s.mkIterator.nextToString = s := by
  sorry

@[simp]
theorem length_next_to_string_next (it : Iterator) : it.next.nextToString.length = it.nextToString.length - 1 := by
  sorry

theorem zero_lt_length_next_to_string_of_has_next {it : Iterator} : it.hasNext → 0 < it.nextToString.length := by
  sorry

end Iterator

end String

