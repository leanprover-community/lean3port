prelude
import Leanbin.Init.Data.List.Lemmas
import Leanbin.Init.Wf

namespace List

def qsort.F {α} (lt : α → α → Bool) : ∀ x : List α, (∀ y : List α, length y < length x → List α) → List α
  | [], IH => []
  | h :: t, IH => by
    induction' e : partition (fun x => lt h x = tt) t with large small
    have : length small < length (h :: t) ∧ length large < length (h :: t) := by
      rw [partition_eq_filter_filter] at e
      injection e
      subst large
      subst small
      constructor <;> exact Nat.succ_le_succₓ (length_le_of_sublist (filter_sublist _))
    exact IH small this.left ++ h :: IH large this.right

def qsort {α} (lt : α → α → Bool) : List α → List α :=
  WellFounded.fix (InvImage.wfₓ length Nat.lt_wf) (Qsort.f lt)

@[simp]
theorem qsort_nil {α} (lt : α → α → Bool) : qsort lt [] = [] := by
  rw [qsort, WellFounded.fix_eq, qsort.F]

@[simp]
theorem qsort_cons {α} (lt : α → α → Bool) h t :
    qsort lt (h :: t) =
      let (large, small) := partitionₓ (fun x => lt h x = tt) t
      qsort lt small ++ h :: qsort lt large :=
  by
  rw [qsort, WellFounded.fix_eq, qsort.F]
  induction' e : partition (fun x => lt h x = tt) t with large small
  simp [e]
  rw [e]

end List

