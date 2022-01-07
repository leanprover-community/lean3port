prelude
import Leanbin.Init.Data.List.Basic
import Leanbin.Init.Function
import Leanbin.Init.Meta.Default
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Meta.Smt.Rsimp

universe u v w w₁ w₂

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

open Nat

@[simp]
theorem nil_append (s : List α) : [] ++ s = s :=
  rfl

@[simp]
theorem cons_append (x : α) (s t : List α) : x :: s ++ t = x :: (s ++ t) :=
  rfl

@[simp]
theorem append_nil (t : List α) : t ++ [] = t := by
  induction t <;> simp [*]

@[simp]
theorem append_assoc (s t u : List α) : s ++ t ++ u = s ++ (t ++ u) := by
  induction s <;> simp [*]

theorem length_cons (a : α) (l : List α) : length (a :: l) = length l + 1 :=
  rfl

@[simp]
theorem length_append (s t : List α) : length (s ++ t) = length s + length t := by
  induction s
  · show length t = 0 + length t
    · rw [Nat.zero_add]
      
    
  · simp [*, Nat.add_comm, Nat.add_left_comm]
    

@[simp]
theorem length_repeat (a : α) (n : ℕ) : length (repeat a n) = n := by
  induction n <;> simp [*] <;> rfl

@[simp]
theorem length_tail (l : List α) : length (tail l) = length l - 1 := by
  cases l <;> rfl

@[simp]
theorem length_drop : ∀ i : ℕ l : List α, length (drop i l) = length l - i
  | 0, l => rfl
  | succ i, [] => Eq.symm (Nat.zero_sub (succ i))
  | succ i, x :: l =>
    calc
      length (drop (succ i) (x :: l)) = length l - i := length_drop i l
      _ = succ (length l) - succ i := (Nat.succ_sub_succ_eq_sub (length l) i).symm
      

theorem map_cons (f : α → β) a l : map f (a :: l) = f a :: map f l :=
  rfl

@[simp]
theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  intro l₁ <;> induction l₁ <;> intros <;> simp [*]

theorem map_singleton (f : α → β) (a : α) : map f [a] = [f a] :=
  rfl

@[simp]
theorem map_id (l : List α) : map id l = l := by
  induction l <;> simp [*]

@[simp]
theorem map_map (g : β → γ) (f : α → β) (l : List α) : map g (map f l) = map (g ∘ f) l := by
  induction l <;> simp [*]

@[simp]
theorem length_map (f : α → β) (l : List α) : length (map f l) = length l := by
  induction l <;> simp [*]

@[simp]
theorem nil_bind (f : α → List β) : List.bind [] f = [] := by
  simp [join, List.bind]

@[simp]
theorem cons_bind x xs (f : α → List β) : List.bind (x :: xs) f = f x ++ List.bind xs f := by
  simp [join, List.bind]

@[simp]
theorem append_bind xs ys (f : α → List β) : List.bind (xs ++ ys) f = List.bind xs f ++ List.bind ys f := by
  induction xs <;> [rfl, simp [*, cons_bind]]

theorem mem_nil_iff (a : α) : a ∈ ([] : List α) ↔ False :=
  Iff.rfl

@[simp]
theorem not_mem_nil (a : α) : a ∉ ([] : List α) :=
  not_false

theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l :=
  Or.inl rfl

@[simp]
theorem mem_cons_iff (a y : α) (l : List α) : a ∈ y :: l ↔ a = y ∨ a ∈ l :=
  Iff.rfl

@[rsimp]
theorem mem_cons_eq (a y : α) (l : List α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
  rfl

theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l := fun H => Or.inr H

theorem eq_or_mem_of_mem_cons {a y : α} {l : List α} : a ∈ y :: l → a = y ∨ a ∈ l := fun h => h

@[simp]
theorem mem_append {a : α} {s t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  induction s <;> simp [*, or_assoc]

@[rsimp]
theorem mem_append_eq (a : α) (s t : List α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
  propext mem_append

theorem mem_append_left {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inl h)

theorem mem_append_right {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inr h)

theorem not_bex_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x := fun ⟨x, hx, px⟩ => hx

theorem ball_nil (p : α → Prop) : ∀, ∀ x ∈ @nil α, ∀, p x := fun x => False.elim

theorem bex_cons (p : α → Prop) (a : α) (l : List α) : (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  ⟨fun ⟨x, h, px⟩ => by
    simp at h
    cases' h with h h
    · cases h
      exact Or.inl px
      
    · exact Or.inr ⟨x, h, px⟩
      ,
    fun o => o.elim (fun pa => ⟨a, mem_cons_self _ _, pa⟩) fun ⟨x, h, px⟩ => ⟨x, mem_cons_of_mem _ h, px⟩⟩

theorem ball_cons (p : α → Prop) (a : α) (l : List α) : (∀, ∀ x ∈ a :: l, ∀, p x) ↔ p a ∧ ∀, ∀ x ∈ l, ∀, p x :=
  ⟨fun al => ⟨al a (mem_cons_self _ _), fun x h => al x (mem_cons_of_mem _ h)⟩, fun ⟨pa, al⟩ x o =>
    o.elim (fun e => e.symm ▸ pa) (al x)⟩

protected def subset (l₁ l₂ : List α) :=
  ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂

instance : HasSubset (List α) :=
  ⟨List.Subset⟩

@[simp]
theorem nil_subset (l : List α) : [] ⊆ l := fun b i => False.elim (Iff.mp (mem_nil_iff b) i)

@[refl, simp]
theorem subset.refl (l : List α) : l ⊆ l := fun b i => i

@[trans]
theorem subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ := fun b i => h₂ (h₁ i)

@[simp]
theorem subset_cons (a : α) (l : List α) : l ⊆ a :: l := fun b i => Or.inr i

theorem subset_of_cons_subset {a : α} {l₁ l₂ : List α} : a :: l₁ ⊆ l₂ → l₁ ⊆ l₂ := fun s b i => s (mem_cons_of_mem _ i)

theorem cons_subset_cons {l₁ l₂ : List α} (a : α) (s : l₁ ⊆ l₂) : a :: l₁ ⊆ a :: l₂ := fun b hin =>
  Or.elim (eq_or_mem_of_mem_cons hin) (fun e : b = a => Or.inl e) fun i : b ∈ l₁ => Or.inr (s i)

@[simp]
theorem subset_append_left (l₁ l₂ : List α) : l₁ ⊆ l₁ ++ l₂ := fun b => mem_append_left _

@[simp]
theorem subset_append_right (l₁ l₂ : List α) : l₂ ⊆ l₁ ++ l₂ := fun b => mem_append_right _

theorem subset_cons_of_subset (a : α) {l₁ l₂ : List α} : l₁ ⊆ l₂ → l₁ ⊆ a :: l₂ := fun s : l₁ ⊆ l₂ a : α i : a ∈ l₁ =>
  Or.inr (s i)

theorem eq_nil_of_length_eq_zero {l : List α} : length l = 0 → l = [] := by
  induction l <;> intros
  rfl
  contradiction

theorem ne_nil_of_length_eq_succ {l : List α} : ∀ {n : Nat}, length l = succ n → l ≠ [] := by
  induction l <;> intros <;> contradiction

@[simp]
theorem length_map₂ (f : α → β → γ) l₁ : ∀ l₂, length (map₂ f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ <;> intro l₂ <;> cases l₂ <;> simp [*, add_one, min_succ_succ, Nat.zero_minₓ, Nat.min_zeroₓ]

@[simp]
theorem length_take : ∀ i : ℕ l : List α, length (take i l) = min i (length l)
  | 0, l => by
    simp [Nat.zero_minₓ]
  | succ n, [] => by
    simp [Nat.min_zeroₓ]
  | succ n, a :: l => by
    simp [*, Nat.min_succ_succₓ, add_one]

theorem length_take_le n (l : List α) : length (take n l) ≤ n := by
  simp [min_le_leftₓ]

theorem length_remove_nth : ∀ l : List α i : ℕ, i < length l → length (remove_nth l i) = length l - 1
  | [], _, h => rfl
  | x :: xs, 0, h => by
    simp [remove_nth]
  | x :: xs, i + 1, h => by
    have : i < length xs := lt_of_succ_lt_succ h
    dsimp [remove_nth] <;>
      rw [length_remove_nth xs i this, Nat.sub_add_cancelₓ (lt_of_le_of_ltₓ (Nat.zero_leₓ _) this)] <;> rfl

@[simp]
theorem partition_eq_filter_filter (p : α → Prop) [DecidablePred p] :
    ∀ l : List α, partition p l = (filter p l, filter (Not ∘ p) l)
  | [] => rfl
  | a :: l => by
    by_cases' pa : p a <;> simp [partition, filter, pa, partition_eq_filter_filter l]

inductive sublist : List α → List α → Prop
  | slnil : sublist [] []
  | cons l₁ l₂ a : sublist l₁ l₂ → sublist l₁ (a :: l₂)
  | cons2 l₁ l₂ a : sublist l₁ l₂ → sublist (a :: l₁) (a :: l₂)

infixl:50 " <+ " => sublist

theorem length_le_of_sublist : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → length l₁ ≤ length l₂
  | _, _, sublist.slnil => le_reflₓ 0
  | _, _, sublist.cons l₁ l₂ a s => le_succ_of_le (length_le_of_sublist s)
  | _, _, sublist.cons2 l₁ l₂ a s => succ_le_succ (length_le_of_sublist s)

@[simp]
theorem filter_nil (p : α → Prop) [h : DecidablePred p] : filter p [] = [] :=
  rfl

@[simp]
theorem filter_cons_of_pos {p : α → Prop} [h : DecidablePred p] {a : α} :
    ∀ l, p a → filter p (a :: l) = a :: filter p l := fun l pa => if_pos pa

@[simp]
theorem filter_cons_of_neg {p : α → Prop} [h : DecidablePred p] {a : α} : ∀ l, ¬p a → filter p (a :: l) = filter p l :=
  fun l pa => if_neg pa

@[simp]
theorem filter_append {p : α → Prop} [h : DecidablePred p] :
    ∀ l₁ l₂ : List α, filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂
  | [], l₂ => rfl
  | a :: l₁, l₂ => by
    by_cases' pa : p a <;> simp [pa, filter_append]

@[simp]
theorem filter_sublist {p : α → Prop} [h : DecidablePred p] : ∀ l : List α, filter p l <+ l
  | [] => sublist.slnil
  | a :: l =>
    if pa : p a then by
      simp [pa] <;> apply sublist.cons2 <;> apply filter_sublist l
    else by
      simp [pa] <;> apply sublist.cons <;> apply filter_sublist l

section MapAccumr

variable {φ : Type w₁} {σ : Type w₂}

def map_accumr (f : α → σ → σ × β) : List α → σ → σ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := map_accumr yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)

@[simp]
theorem length_map_accumr : ∀ f : α → σ → σ × β x : List α s : σ, length (map_accumr f x s).2 = length x
  | f, a :: x, s => congr_argₓ succ (length_map_accumr f x s)
  | f, [], s => rfl

end MapAccumr

section MapAccumr₂

variable {φ : Type w₁} {σ : Type w₂}

def map_accumr₂ (f : α → β → σ → σ × φ) : List α → List β → σ → σ × List φ
  | [], _, c => (c, [])
  | _, [], c => (c, [])
  | x :: xr, y :: yr, c =>
    let r := map_accumr₂ xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)

@[simp]
theorem length_map_accumr₂ : ∀ f : α → β → σ → σ × φ x y c, length (map_accumr₂ f x y c).2 = min (length x) (length y)
  | f, a :: x, b :: y, c =>
    calc
      succ (length (map_accumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congr_argₓ succ (length_map_accumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (min_succ_succ (length x) (length y))
      
  | f, a :: x, [], c => rfl
  | f, [], b :: y, c => rfl
  | f, [], [], c => rfl

end MapAccumr₂

end List

