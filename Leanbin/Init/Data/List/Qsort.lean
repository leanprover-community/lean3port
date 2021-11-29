prelude 
import Leanbin.Init.Data.List.Lemmas 
import Leanbin.Init.Wf

namespace List

-- error in Init.Data.List.Qsort: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
def qsort.F {α} (lt : α → α → bool) : ∀ x : list α, ∀ y : list α, «expr < »(length y, length x) → list α → list α
| «expr[ , ]»([]), IH := «expr[ , ]»([])
| «expr :: »(h, t), IH := begin
  induction [expr e, ":", expr partition (λ x, «expr = »(lt h x, tt)) t] [] ["with", ident large, ident small] [],
  have [] [":", expr «expr ∧ »(«expr < »(length small, length «expr :: »(h, t)), «expr < »(length large, length «expr :: »(h, t)))] [],
  { rw [expr partition_eq_filter_filter] ["at", ident e],
    injection [expr e] [],
    subst [expr large],
    subst [expr small],
    constructor; exact [expr nat.succ_le_succ (length_le_of_sublist (filter_sublist _))] },
  exact [expr «expr ++ »(IH small this.left, «expr :: »(h, IH large this.right))]
end

def qsort {α} (lt : α → α → Bool) : List α → List α :=
  WellFounded.fix (InvImage.wfₓ length Nat.lt_wf) (qsort.F lt)

@[simp]
theorem qsort_nil {α} (lt : α → α → Bool) : qsort lt [] = [] :=
  by 
    rw [qsort, WellFounded.fix_eq, qsort.F]

@[simp]
theorem qsort_cons {α} (lt : α → α → Bool) h t :
  qsort lt (h :: t) =
    let (large, small) := partition (fun x => lt h x = tt) t 
    qsort lt small ++ h :: qsort lt large :=
  by 
    rw [qsort, WellFounded.fix_eq, qsort.F]
    induction' e : partition (fun x => lt h x = tt) t with large small 
    simp [e]
    rw [e]

end List

