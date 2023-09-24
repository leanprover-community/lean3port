/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.List.Lemmas
import Init.Wf

#align_import init.data.list.qsort from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

namespace List

-- Note: we can't use the equation compiler here because
-- init.meta.well_founded_tactics uses this file
def Qsort.f {α} (lt : α → α → Bool) :
    ∀ x : List α, (∀ y : List α, length y < length x → List α) → List α
  | [], IH => []
  | h :: t, IH =>
    by
    induction' e : partition (fun x => lt h x = tt) t with large small
    have : length Small < length (h :: t) ∧ length large < length (h :: t) :=
      by
      rw [partition_eq_filter_filter] at e 
      injection e
      subst large; subst Small
      constructor <;> exact Nat.succ_le_succ (length_le_of_sublist (filter_sublist _))
    exact IH Small this.left ++ h :: IH large this.right
#align list.qsort.F List.Qsort.f

/-- This is based on the minimalist Haskell "quicksort".

   Remark: this is *not* really quicksort since it doesn't partition the elements in-place -/
def qsort {α} (lt : α → α → Bool) : List α → List α :=
  WellFounded.fix (InvImage.wf length Nat.lt_wfRel) (Qsort.f lt)
#align list.qsort List.qsort

@[simp]
theorem qsort_nil {α} (lt : α → α → Bool) : qsort lt [] = [] := by
  rw [qsort, WellFounded.fix_eq, qsort.F]
#align list.qsort_nil List.qsort_nil

@[simp]
theorem qsort_cons {α} (lt : α → α → Bool) (h t) :
    qsort lt (h :: t) =
      let (large, Small) := partition (fun x => lt h x = true) t
      qsort lt Small ++ h :: qsort lt large :=
  by
  rw [qsort, WellFounded.fix_eq, qsort.F]
  induction' e : partition (fun x => lt h x = tt) t with large small
  simp [e]; rw [e]
#align list.qsort_cons List.qsort_cons

end List

