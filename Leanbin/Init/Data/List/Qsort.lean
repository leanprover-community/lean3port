/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.list.qsort
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.List.Lemmas
import Leanbin.Init.Wf

namespace List

-- Note: we can't use the equation compiler here because
-- init.meta.well_founded_tactics uses this file
def Qsort.f {α} (lt : α → α → Bool) :
    ∀ x : List α, (∀ y : List α, length y < length x → List α) → List α
  | [], IH => []
  | h :: t, IH => by
    induction' e : partition (fun x => lt h x = tt) t with large small
    have : length small < length (h :: t) ∧ length large < length (h :: t) := by
      rw [partition_eq_filter_filter] at e
      injection e
      subst large
      subst small
      constructor <;> exact Nat.succ_le_succ (length_le_of_sublist (filter_sublist _))
    exact IH small this.left ++ h :: IH large this.right
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
      let (large, small) := partition (fun x => lt h x = tt) t
      qsort lt small ++ h :: qsort lt large :=
  by 
  rw [qsort, WellFounded.fix_eq, qsort.F]
  induction' e : partition (fun x => lt h x = tt) t with large small
  simp [e]; rw [e]
#align list.qsort_cons List.qsort_cons

end List

