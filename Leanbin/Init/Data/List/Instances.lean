prelude
import Leanbin.Init.Data.List.Lemmas

open List

universe u v

attribute [local simp] join List.ret

instance : Monadₓ List where
  pure := @List.ret
  map := @List.map
  bind := @List.bind

instance : IsLawfulMonad List where
  bind_pure_comp_eq_map := by
    intro α β f l
    induction l <;> simp_all [· <$> ·, · >>= ·, pure]
  id_map := @List.map_id
  pure_bind := by
    intros
    simp [pure, · >>= ·]
  bind_assoc := by
    intro α β γ l f g
    induction' l with x l ih
    · simp [· >>= ·]
      
    · simp [· >>= ·] at ih
      simp [· >>= ·, ih]
      

instance : Alternativeₓ List :=
  { List.monad with failure := @List.nil, orelse := @List.append }

namespace List

variable {α β : Type u} (p : α → Prop) [DecidablePred p]

instance bin_tree_to_list : Coe (BinTree α) (List α) :=
  ⟨BinTree.toList⟩

instance decidable_bex : ∀ l : List α, Decidable (∃ x ∈ l, p x)
  | [] =>
    is_false
      (by
        simp [List.not_bex_nilₓ])
  | x :: xs =>
    if h₁ : p x then is_true ⟨x, mem_cons_self _ _, h₁⟩
    else
      match decidable_bex xs with
      | is_true h₂ =>
        is_true
          (by
            cases' h₂ with y h
            cases' h with hm hp
            exact ⟨y, mem_cons_of_mem _ hm, hp⟩)
      | is_false h₂ =>
        is_false
          (by
            intro h
            cases' h with y h
            cases' h with hm hp
            cases eq_or_mem_of_mem_cons hm
            · rw [h] at hp
              contradiction
              
            · refine' absurd _ h₂
              exact ⟨y, h, hp⟩
              )

instance decidable_ball (l : List α) : Decidable (∀, ∀ x ∈ l, ∀, p x) :=
  if h : ∃ x ∈ l, ¬p x then
    is_false $
      let ⟨x, h, np⟩ := h
      fun al => np (al x h)
  else is_true $ fun x hx => if h' : p x then h' else False.elim $ h ⟨x, hx, h'⟩

end List

