/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.List.Lemmas
import Leanbin.Init.Wf

namespace List

/- This is based on the minimalist Haskell "quicksort".

   Remark: this is *not* really quicksort since it doesn't partition the elements in-place -/
def qsort (lt : α → α → Bool) : List α → List α
  | [] => []
  | h :: t =>
    match e : partition (lt h) t with
    | (large, small) =>
    have : length small < length (h :: t) ∧ length large < length (h :: t) := by
      rw [partition_eq_filter_filter] at e
      injection e
      subst large
      subst small
      constructor <;> exact Nat.succ_le_succ (length_le_of_sublist (filter_sublist _))
    have _left := this.left
    have _right := this.right
    qsort lt small ++ h :: qsort lt large
termination_by
  qsort lt l => l.length

@[simp]
theorem qsort_nil {α} (lt : α → α → Bool) : qsort lt [] = [] := by
  rw [qsort]

@[simp]
theorem qsort_cons {α} (lt : α → α → Bool) (h t) :
    qsort lt (h :: t) =
      let (large, small) := partition (lt h) t
      qsort lt small ++ h :: qsort lt large := by
  rw [qsort]

end List

