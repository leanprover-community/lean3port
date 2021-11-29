prelude 
import Leanbin.Init.Data.Nat.Basic 
import Leanbin.Init.Data.Nat.Div 
import Leanbin.Init.Meta.Default 
import Leanbin.Init.Algebra.Functions

universe u

namespace Nat

attribute [pre_smt] nat_zero_eq_zero

/-! addition -/


protected theorem add_comm : ∀ n m : ℕ, (n+m) = m+n
| n, 0 => Eq.symm (Nat.zero_add n)
| n, m+1 =>
  suffices succ (n+m) = succ (m+n) from Eq.symm (succ_add m n) ▸ this 
  congr_argₓ succ (add_comm n m)

protected theorem add_assoc : ∀ n m k : ℕ, ((n+m)+k) = n+m+k
| n, m, 0 => rfl
| n, m, succ k =>
  by 
    rw [add_succ, add_succ, add_assoc] <;> rfl

protected theorem add_left_comm : ∀ n m k : ℕ, (n+m+k) = m+n+k :=
  left_comm Nat.add Nat.add_comm Nat.add_assoc

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected theorem add_left_cancel : ∀ {n m k : exprℕ()}, «expr = »(«expr + »(n, m), «expr + »(n, k)) → «expr = »(m, k)
| 0, m, k := by simp [] [] [] ["[", expr nat.zero_add, "]"] [] [] { contextual := tt }
| succ n, m, k := λ
h, have «expr = »(«expr + »(n, m), «expr + »(n, k)), by { simp [] [] [] ["[", expr succ_add, "]"] [] ["at", ident h],
  assumption },
add_left_cancel this

protected theorem add_right_cancel {n m k : ℕ} (h : (n+m) = k+m) : n = k :=
  have  : (m+n) = m+k :=
    by 
      rwa [Nat.add_comm n m, Nat.add_comm k m] at h 
  Nat.add_left_cancel this

theorem succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
  fun h => Nat.noConfusion h

theorem succ_ne_self : ∀ n : ℕ, succ n ≠ n
| 0, h => absurd h (Nat.succ_ne_zero 0)
| n+1, h => succ_ne_self n (Nat.noConfusion h fun h => h)

protected theorem one_ne_zero : 1 ≠ (0 : ℕ) :=
  fun h => Nat.noConfusion h

protected theorem zero_ne_one : 0 ≠ (1 : ℕ) :=
  fun h => Nat.noConfusion h

protected theorem eq_zero_of_add_eq_zero_right : ∀ {n m : ℕ}, (n+m) = 0 → n = 0
| 0, m =>
  by 
    simp [Nat.zero_add]
| n+1, m =>
  fun h =>
    by 
      exfalso 
      rw [add_one, succ_add] at h 
      apply succ_ne_zero _ h

protected theorem eq_zero_of_add_eq_zero_left {n m : ℕ} (h : (n+m) = 0) : m = 0 :=
  @Nat.eq_zero_of_add_eq_zero_right m n (Nat.add_comm n m ▸ h)

protected theorem add_right_comm : ∀ n m k : ℕ, ((n+m)+k) = (n+k)+m :=
  right_comm Nat.add Nat.add_comm Nat.add_assoc

theorem eq_zero_of_add_eq_zero {n m : ℕ} (H : (n+m) = 0) : n = 0 ∧ m = 0 :=
  ⟨Nat.eq_zero_of_add_eq_zero_right H, Nat.eq_zero_of_add_eq_zero_left H⟩

/-! multiplication -/


protected theorem mul_zero (n : ℕ) : (n*0) = 0 :=
  rfl

theorem mul_succ (n m : ℕ) : (n*succ m) = (n*m)+n :=
  rfl

protected theorem zero_mul : ∀ n : ℕ, (0*n) = 0
| 0 => rfl
| succ n =>
  by 
    rw [mul_succ, zero_mul]

private unsafe def sort_add :=
  sorry

theorem succ_mul : ∀ n m : ℕ, (succ n*m) = (n*m)+m
| n, 0 => rfl
| n, succ m =>
  by 
    simp [mul_succ, add_succ, succ_mul n m]
    runTac 
      sort_add

protected theorem right_distrib : ∀ n m k : ℕ, ((n+m)*k) = (n*k)+m*k
| n, m, 0 => rfl
| n, m, succ k =>
  by 
    simp [mul_succ, right_distrib n m k]
    runTac 
      sort_add

protected theorem left_distrib : ∀ n m k : ℕ, (n*m+k) = (n*m)+n*k
| 0, m, k =>
  by 
    simp [Nat.zero_mul]
| succ n, m, k =>
  by 
    simp [succ_mul, left_distrib n m k]
    runTac 
      sort_add

protected theorem mul_comm : ∀ n m : ℕ, (n*m) = m*n
| n, 0 =>
  by 
    rw [Nat.zero_mul, Nat.mul_zero]
| n, succ m =>
  by 
    simp [mul_succ, succ_mul, mul_comm n m]

protected theorem mul_assoc : ∀ n m k : ℕ, ((n*m)*k) = n*m*k
| n, m, 0 => rfl
| n, m, succ k =>
  by 
    simp [mul_succ, Nat.left_distrib, mul_assoc n m k]

protected theorem mul_one : ∀ n : ℕ, (n*1) = n :=
  Nat.zero_add

protected theorem one_mul (n : ℕ) : (1*n) = n :=
  by 
    rw [Nat.mul_comm, Nat.mul_one]

theorem succ_add_eq_succ_add (n m : ℕ) : (succ n+m) = n+succ m :=
  by 
    simp [succ_add, add_succ]

theorem eq_zero_of_mul_eq_zero : ∀ {n m : ℕ}, (n*m) = 0 → n = 0 ∨ m = 0
| 0, m => fun h => Or.inl rfl
| succ n, m =>
  by 
    rw [succ_mul]
    intro h 
    exact Or.inr (Nat.eq_zero_of_add_eq_zero_left h)

/-! properties of inequality -/


protected theorem le_of_eqₓ {n m : ℕ} (p : n = m) : n ≤ m :=
  p ▸ less_than_or_equal.refl

theorem le_succ_of_le {n m : ℕ} (h : n ≤ m) : n ≤ succ m :=
  Nat.le_transₓ h (le_succ m)

theorem le_of_succ_le {n m : ℕ} (h : succ n ≤ m) : n ≤ m :=
  Nat.le_transₓ (le_succ n) h

protected theorem le_of_ltₓ {n m : ℕ} (h : n < m) : n ≤ m :=
  le_of_succ_le h

theorem lt.step {n m : ℕ} : n < m → n < succ m :=
  less_than_or_equal.step

protected theorem eq_zero_or_pos (n : ℕ) : n = 0 ∨ 0 < n :=
  by 
    cases n 
    exact Or.inl rfl 
    exact Or.inr (succ_pos _)

protected theorem pos_of_ne_zero {n : Nat} : n ≠ 0 → 0 < n :=
  Or.resolve_left n.eq_zero_or_pos

protected theorem lt_transₓ {n m k : ℕ} (h₁ : n < m) : m < k → n < k :=
  Nat.le_transₓ (less_than_or_equal.step h₁)

protected theorem lt_of_le_of_ltₓ {n m k : ℕ} (h₁ : n ≤ m) : m < k → n < k :=
  Nat.le_transₓ (succ_le_succ h₁)

theorem lt.base (n : ℕ) : n < succ n :=
  Nat.le_reflₓ (succ n)

theorem lt_succ_self (n : ℕ) : n < succ n :=
  lt.base n

protected theorem le_antisymmₓ {n m : ℕ} (h₁ : n ≤ m) : m ≤ n → n = m :=
  less_than_or_equal.cases_on h₁ (fun a => rfl) fun a b c => absurd (Nat.lt_of_le_of_ltₓ b c) (Nat.lt_irreflₓ n)

protected theorem lt_or_geₓ : ∀ a b : ℕ, a < b ∨ b ≤ a
| a, 0 => Or.inr a.zero_le
| a, b+1 =>
  match lt_or_geₓ a b with 
  | Or.inl h => Or.inl (le_succ_of_le h)
  | Or.inr h =>
    match Nat.eq_or_lt_of_leₓ h with 
    | Or.inl h1 => Or.inl (h1 ▸ lt_succ_self b)
    | Or.inr h1 => Or.inr h1

protected theorem le_totalₓ {m n : ℕ} : m ≤ n ∨ n ≤ m :=
  Or.imp_left Nat.le_of_ltₓ (Nat.lt_or_geₓ m n)

protected theorem lt_of_le_and_ne {m n : ℕ} (h1 : m ≤ n) : m ≠ n → m < n :=
  Or.resolve_right (Or.swap (Nat.eq_or_lt_of_leₓ h1))

protected theorem lt_iff_le_not_leₓ {m n : ℕ} : m < n ↔ m ≤ n ∧ ¬n ≤ m :=
  ⟨fun hmn => ⟨Nat.le_of_ltₓ hmn, fun hnm => Nat.lt_irreflₓ _ (Nat.lt_of_le_of_ltₓ hnm hmn)⟩,
    fun ⟨hmn, hnm⟩ => Nat.lt_of_le_and_neₓ hmn fun heq => hnm (HEq ▸ Nat.le_reflₓ _)⟩

instance : LinearOrderₓ ℕ :=
  { le := Nat.LessThanOrEqual, le_refl := @Nat.le_reflₓ, le_trans := @Nat.le_transₓ, le_antisymm := @Nat.le_antisymmₓ,
    le_total := @Nat.le_totalₓ, lt := Nat.Lt, lt_iff_le_not_le := @Nat.lt_iff_le_not_leₓ,
    decidableLt := Nat.decidableLt, decidableLe := Nat.decidableLe, DecidableEq := Nat.decidableEq }

protected theorem eq_zero_of_le_zero {n : Nat} (h : n ≤ 0) : n = 0 :=
  le_antisymmₓ h n.zero_le

theorem succ_lt_succ {a b : ℕ} : a < b → succ a < succ b :=
  succ_le_succ

theorem lt_of_succ_lt {a b : ℕ} : succ a < b → a < b :=
  le_of_succ_le

theorem lt_of_succ_lt_succ {a b : ℕ} : succ a < succ b → a < b :=
  le_of_succ_le_succ

theorem pred_lt_pred : ∀ {n m : ℕ}, n ≠ 0 → n < m → pred n < pred m
| 0, _, h₁, h => absurd rfl h₁
| n, 0, h₁, h => absurd h n.not_lt_zero
| succ n, succ m, _, h => lt_of_succ_lt_succ h

theorem lt_of_succ_le {a b : ℕ} (h : succ a ≤ b) : a < b :=
  h

theorem succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b :=
  h

protected theorem le_add_right : ∀ n k : ℕ, n ≤ n+k
| n, 0 => Nat.le_reflₓ n
| n, k+1 => le_succ_of_le (le_add_right n k)

protected theorem le_add_left (n m : ℕ) : n ≤ m+n :=
  Nat.add_comm n m ▸ n.le_add_right m

theorem le.dest : ∀ {n m : ℕ}, n ≤ m → ∃ k, (n+k) = m
| n, _, less_than_or_equal.refl => ⟨0, rfl⟩
| n, _, less_than_or_equal.step h =>
  match le.dest h with 
  | ⟨w, hw⟩ => ⟨succ w, hw ▸ add_succ n w⟩

protected theorem le.intro {n m k : ℕ} (h : (n+k) = m) : n ≤ m :=
  h ▸ n.le_add_right k

protected theorem add_le_add_left {n m : ℕ} (h : n ≤ m) (k : ℕ) : (k+n) ≤ k+m :=
  match le.dest h with 
  | ⟨w, hw⟩ =>
    @le.intro _ _ w
      (by 
        rw [Nat.add_assoc, hw])

protected theorem add_le_add_right {n m : ℕ} (h : n ≤ m) (k : ℕ) : (n+k) ≤ m+k :=
  by 
    rw [Nat.add_comm n k, Nat.add_comm m k]
    apply Nat.add_le_add_leftₓ h

protected theorem le_of_add_le_add_left {k n m : ℕ} (h : (k+n) ≤ k+m) : n ≤ m :=
  match le.dest h with 
  | ⟨w, hw⟩ =>
    @le.intro _ _ w
      (by 
        rw [Nat.add_assoc] at hw 
        apply Nat.add_left_cancel hw)

protected theorem le_of_add_le_add_right {k n m : ℕ} : ((n+k) ≤ m+k) → n ≤ m :=
  by 
    rw [Nat.add_comm _ k, Nat.add_comm _ k]
    apply Nat.le_of_add_le_add_leftₓ

protected theorem add_le_add_iff_le_right (k n m : ℕ) : ((n+k) ≤ m+k) ↔ n ≤ m :=
  ⟨Nat.le_of_add_le_add_rightₓ, fun h => Nat.add_le_add_rightₓ h _⟩

protected theorem lt_of_add_lt_add_left {k n m : ℕ} (h : (k+n) < k+m) : n < m :=
  let h' := Nat.le_of_ltₓ h 
  Nat.lt_of_le_and_neₓ (Nat.le_of_add_le_add_leftₓ h')
    fun heq =>
      Nat.lt_irreflₓ (k+m)
        (by 
          rw [HEq] at h 
          assumption)

protected theorem lt_of_add_lt_add_right {a b c : ℕ} (h : (a+b) < c+b) : a < c :=
  Nat.lt_of_add_lt_add_leftₓ$
    show (b+a) < b+c by 
      rwa [Nat.add_comm b a, Nat.add_comm b c]

protected theorem add_lt_add_left {n m : ℕ} (h : n < m) (k : ℕ) : (k+n) < k+m :=
  lt_of_succ_le (add_succ k n ▸ Nat.add_le_add_leftₓ (succ_le_of_lt h) k)

protected theorem add_lt_add_right {n m : ℕ} (h : n < m) (k : ℕ) : (n+k) < m+k :=
  Nat.add_comm k m ▸ Nat.add_comm k n ▸ Nat.add_lt_add_leftₓ h k

protected theorem lt_add_of_pos_right {n k : ℕ} (h : 0 < k) : n < n+k :=
  Nat.add_lt_add_leftₓ h n

protected theorem lt_add_of_pos_left {n k : ℕ} (h : 0 < k) : n < k+n :=
  by 
    rw [Nat.add_comm] <;> exact Nat.lt_add_of_pos_rightₓ h

protected theorem add_lt_add {a b c d : ℕ} (h₁ : a < b) (h₂ : c < d) : (a+c) < b+d :=
  lt_transₓ (Nat.add_lt_add_rightₓ h₁ c) (Nat.add_lt_add_leftₓ h₂ b)

protected theorem add_le_add {a b c d : ℕ} (h₁ : a ≤ b) (h₂ : c ≤ d) : (a+c) ≤ b+d :=
  le_transₓ (Nat.add_le_add_rightₓ h₁ c) (Nat.add_le_add_leftₓ h₂ b)

protected theorem zero_lt_one : 0 < (1 : Nat) :=
  zero_lt_succ 0

protected theorem mul_le_mul_left {n m : ℕ} (k : ℕ) (h : n ≤ m) : (k*n) ≤ k*m :=
  match le.dest h with 
  | ⟨l, hl⟩ =>
    have  : ((k*n)+k*l) = k*m :=
      by 
        rw [←Nat.left_distrib, hl]
    le.intro this

protected theorem mul_le_mul_right {n m : ℕ} (k : ℕ) (h : n ≤ m) : (n*k) ≤ m*k :=
  Nat.mul_comm k m ▸ Nat.mul_comm k n ▸ k.mul_le_mul_left h

protected theorem mul_lt_mul_of_pos_left {n m k : ℕ} (h : n < m) (hk : 0 < k) : (k*n) < k*m :=
  Nat.lt_of_lt_of_leₓ (Nat.lt_add_of_pos_rightₓ hk) (mul_succ k n ▸ Nat.mul_le_mul_leftₓ k (succ_le_of_lt h))

protected theorem mul_lt_mul_of_pos_right {n m k : ℕ} (h : n < m) (hk : 0 < k) : (n*k) < m*k :=
  Nat.mul_comm k m ▸ Nat.mul_comm k n ▸ Nat.mul_lt_mul_of_pos_leftₓ h hk

protected theorem le_of_mul_le_mul_left {a b c : ℕ} (h : (c*a) ≤ c*b) (hc : 0 < c) : a ≤ b :=
  not_ltₓ.1
    fun h1 : b < a =>
      have h2 : (c*b) < c*a := Nat.mul_lt_mul_of_pos_leftₓ h1 hc 
      not_le_of_gtₓ h2 h

theorem le_of_lt_succ {m n : Nat} : m < succ n → m ≤ n :=
  le_of_succ_le_succ

protected theorem eq_of_mul_eq_mul_left {m k n : ℕ} (Hn : 0 < n) (H : (n*m) = n*k) : m = k :=
  le_antisymmₓ (Nat.le_of_mul_le_mul_leftₓ (le_of_eqₓ H) Hn) (Nat.le_of_mul_le_mul_leftₓ (le_of_eqₓ H.symm) Hn)

protected theorem mul_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 < a*b :=
  have h : (0*b) < a*b := Nat.mul_lt_mul_of_pos_rightₓ ha hb 
  by 
    rwa [Nat.zero_mul] at h

theorem le_succ_of_pred_le {n m : ℕ} : pred n ≤ m → n ≤ succ m :=
  Nat.casesOn n less_than_or_equal.step fun a => succ_le_succ

theorem le_lt_antisymm {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n) : False :=
  Nat.lt_irreflₓ n (Nat.lt_of_le_of_ltₓ h₁ h₂)

theorem lt_le_antisymm {n m : ℕ} (h₁ : n < m) (h₂ : m ≤ n) : False :=
  le_lt_antisymm h₂ h₁

protected theorem lt_asymmₓ {n m : ℕ} (h₁ : n < m) : ¬m < n :=
  le_lt_antisymm (Nat.le_of_ltₓ h₁)

protected def lt_ge_by_cases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : b ≤ a → C) : C :=
  Decidable.byCases h₁ fun h => h₂ (Or.elim (Nat.lt_or_geₓ a b) (fun a => absurd a h) fun a => a)

protected def ltByCases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a = b → C) (h₃ : b < a → C) : C :=
  Nat.ltGeByCases h₁ fun h₁ => Nat.ltGeByCases h₃ fun h => h₂ (Nat.le_antisymmₓ h h₁)

protected theorem lt_trichotomyₓ (a b : ℕ) : a < b ∨ a = b ∨ b < a :=
  Nat.ltByCases (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr h)

protected theorem eq_or_lt_of_not_ltₓ {a b : ℕ} (hnlt : ¬a < b) : a = b ∨ b < a :=
  (Nat.lt_trichotomyₓ a b).resolve_left hnlt

theorem lt_succ_of_lt {a b : Nat} (h : a < b) : a < succ b :=
  le_succ_of_le h

theorem one_pos : 0 < 1 :=
  Nat.zero_lt_oneₓ

protected theorem mul_le_mul_of_nonneg_left {a b c : ℕ} (h₁ : a ≤ b) : (c*a) ≤ c*b :=
  by 
    byCases' hba : b ≤ a
    ·
      simp [le_antisymmₓ hba h₁]
    byCases' hc0 : c ≤ 0
    ·
      simp [le_antisymmₓ hc0 c.zero_le, Nat.zero_mul]
    exact
      (le_not_le_of_ltₓ (Nat.mul_lt_mul_of_pos_leftₓ (lt_of_le_not_leₓ h₁ hba) (lt_of_le_not_leₓ c.zero_le hc0))).left

protected theorem mul_le_mul_of_nonneg_right {a b c : ℕ} (h₁ : a ≤ b) : (a*c) ≤ b*c :=
  by 
    byCases' hba : b ≤ a
    ·
      simp [le_antisymmₓ hba h₁]
    byCases' hc0 : c ≤ 0
    ·
      simp [le_antisymmₓ hc0 c.zero_le, Nat.mul_zero]
    exact
      (le_not_le_of_ltₓ (Nat.mul_lt_mul_of_pos_rightₓ (lt_of_le_not_leₓ h₁ hba) (lt_of_le_not_leₓ c.zero_le hc0))).left

protected theorem mul_lt_mul {a b c d : ℕ} (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b) : (a*b) < c*d :=
  calc (a*b) < c*b := Nat.mul_lt_mul_of_pos_rightₓ hac pos_b 
    _ ≤ c*d := Nat.mul_le_mul_of_nonneg_leftₓ hbd
    

protected theorem mul_lt_mul' {a b c d : ℕ} (h1 : a ≤ c) (h2 : b < d) (h3 : 0 < c) : (a*b) < c*d :=
  calc (a*b) ≤ c*b := Nat.mul_le_mul_of_nonneg_rightₓ h1 
    _ < c*d := Nat.mul_lt_mul_of_pos_leftₓ h2 h3
    

protected theorem mul_le_mul {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) : (a*b) ≤ c*d :=
  calc (a*b) ≤ c*b := Nat.mul_le_mul_of_nonneg_rightₓ hac 
    _ ≤ c*d := Nat.mul_le_mul_of_nonneg_leftₓ hbd
    

/-! bit0/bit1 properties -/


protected theorem bit1_eq_succ_bit0 (n : ℕ) : bit1 n = succ (bit0 n) :=
  rfl

protected theorem bit1_succ_eq (n : ℕ) : bit1 (succ n) = succ (succ (bit1 n)) :=
  Eq.trans (Nat.bit1_eq_succ_bit0 (succ n)) (congr_argₓ succ (Nat.bit0_succ_eq n))

protected theorem bit1_ne_one : ∀ {n : ℕ}, n ≠ 0 → bit1 n ≠ 1
| 0, h, h1 => absurd rfl h
| n+1, h, h1 => Nat.noConfusion h1 fun h2 => absurd h2 (succ_ne_zero _)

protected theorem bit0_ne_one : ∀ n : ℕ, bit0 n ≠ 1
| 0, h => absurd h (Ne.symm Nat.one_ne_zero)
| n+1, h =>
  have h1 : succ (succ (n+n)) = 1 := succ_add n n ▸ h 
  Nat.noConfusion h1 fun h2 => absurd h2 (succ_ne_zero (n+n))

protected theorem add_self_ne_one : ∀ n : ℕ, (n+n) ≠ 1
| 0, h => Nat.noConfusion h
| n+1, h =>
  have h1 : succ (succ (n+n)) = 1 := succ_add n n ▸ h 
  Nat.noConfusion h1 fun h2 => absurd h2 (Nat.succ_ne_zero (n+n))

protected theorem bit1_ne_bit0 : ∀ n m : ℕ, bit1 n ≠ bit0 m
| 0, m, h => absurd h (Ne.symm (Nat.add_self_ne_one m))
| n+1, 0, h =>
  have h1 : succ (bit0 (succ n)) = 0 := h 
  absurd h1 (Nat.succ_ne_zero _)
| n+1, m+1, h =>
  have h1 : succ (succ (bit1 n)) = succ (succ (bit0 m)) := Nat.bit0_succ_eq m ▸ Nat.bit1_succ_eq n ▸ h 
  have h2 : bit1 n = bit0 m := Nat.noConfusion h1 fun h2' => Nat.noConfusion h2' fun h2'' => h2'' 
  absurd h2 (bit1_ne_bit0 n m)

protected theorem bit0_ne_bit1 : ∀ n m : ℕ, bit0 n ≠ bit1 m :=
  fun n m : Nat => Ne.symm (Nat.bit1_ne_bit0 m n)

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected theorem bit0_inj : ∀ {n m : exprℕ()}, «expr = »(bit0 n, bit0 m) → «expr = »(n, m)
| 0, 0, h := rfl
| 0, «expr + »(m, 1), h := by contradiction
| «expr + »(n, 1), 0, h := by contradiction
| «expr + »(n, 1), «expr + »(m, 1), h := have «expr = »(succ (succ «expr + »(n, n)), succ (succ «expr + »(m, m))), by { unfold [ident bit0] ["at", ident h],
  simp [] [] [] ["[", expr add_one, ",", expr add_succ, ",", expr succ_add, "]"] [] ["at", ident h],
  have [ident aux] [":", expr «expr = »(«expr + »(n, n), «expr + »(m, m))] [":=", expr h],
  rw [expr aux] [] },
have «expr = »(«expr + »(n, n), «expr + »(m, m)), by iterate [] { injection [expr this] ["with", ident this] },
have «expr = »(n, m), from bit0_inj this,
by rw [expr this] []

protected theorem bit1_inj : ∀ {n m : ℕ}, bit1 n = bit1 m → n = m :=
  fun n m h =>
    have  : succ (bit0 n) = succ (bit0 m) :=
      by 
        simp [Nat.bit1_eq_succ_bit0] at h 
        rw [h]
    have  : bit0 n = bit0 m :=
      by 
        injection this 
    Nat.bit0_inj this

protected theorem bit0_ne {n m : ℕ} : n ≠ m → bit0 n ≠ bit0 m :=
  fun h₁ h₂ => absurd (Nat.bit0_inj h₂) h₁

protected theorem bit1_ne {n m : ℕ} : n ≠ m → bit1 n ≠ bit1 m :=
  fun h₁ h₂ => absurd (Nat.bit1_inj h₂) h₁

protected theorem zero_ne_bit0 {n : ℕ} : n ≠ 0 → 0 ≠ bit0 n :=
  fun h => Ne.symm (Nat.bit0_ne_zero h)

protected theorem zero_ne_bit1 (n : ℕ) : 0 ≠ bit1 n :=
  Ne.symm (Nat.bit1_ne_zero n)

protected theorem one_ne_bit0 (n : ℕ) : 1 ≠ bit0 n :=
  Ne.symm (Nat.bit0_ne_one n)

protected theorem one_ne_bit1 {n : ℕ} : n ≠ 0 → 1 ≠ bit1 n :=
  fun h => Ne.symm (Nat.bit1_ne_one h)

protected theorem one_lt_bit1 : ∀ {n : Nat}, n ≠ 0 → 1 < bit1 n
| 0, h =>
  by 
    contradiction
| succ n, h =>
  by 
    rw [Nat.bit1_succ_eq]
    apply succ_lt_succ 
    apply zero_lt_succ

protected theorem one_lt_bit0 : ∀ {n : Nat}, n ≠ 0 → 1 < bit0 n
| 0, h =>
  by 
    contradiction
| succ n, h =>
  by 
    rw [Nat.bit0_succ_eq]
    apply succ_lt_succ 
    apply zero_lt_succ

protected theorem bit0_lt {n m : Nat} (h : n < m) : bit0 n < bit0 m :=
  Nat.add_lt_addₓ h h

protected theorem bit1_lt {n m : Nat} (h : n < m) : bit1 n < bit1 m :=
  succ_lt_succ (Nat.add_lt_addₓ h h)

protected theorem bit0_lt_bit1 {n m : Nat} (h : n ≤ m) : bit0 n < bit1 m :=
  lt_succ_of_le (Nat.add_le_addₓ h h)

protected theorem bit1_lt_bit0 : ∀ {n m : Nat}, n < m → bit1 n < bit0 m
| n, 0, h => absurd h n.not_lt_zero
| n, succ m, h =>
  have  : n ≤ m := le_of_lt_succ h 
  have  : succ (n+n) ≤ succ (m+m) := succ_le_succ (Nat.add_le_addₓ this this)
  have  : succ (n+n) ≤ succ m+m :=
    by 
      rw [succ_add]
      assumption 
  show succ (n+n) < succ (succ m+m) from lt_succ_of_le this

protected theorem one_le_bit1 (n : ℕ) : 1 ≤ bit1 n :=
  show 1 ≤ succ (bit0 n) from succ_le_succ (bit0 n).zero_le

protected theorem one_le_bit0 : ∀ n : ℕ, n ≠ 0 → 1 ≤ bit0 n
| 0, h => absurd rfl h
| n+1, h =>
  suffices 1 ≤ succ (succ (bit0 n)) from Eq.symm (Nat.bit0_succ_eq n) ▸ this 
  succ_le_succ (bit0 n).succ.zero_le

/-! successor and predecessor -/


@[simp]
theorem pred_zero : pred 0 = 0 :=
  rfl

@[simp]
theorem pred_succ (n : ℕ) : pred (succ n) = n :=
  rfl

theorem add_one_ne_zero (n : ℕ) : (n+1) ≠ 0 :=
  succ_ne_zero _

theorem eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
  by 
    cases n <;> simp 

theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : ∃ k : ℕ, n = succ k :=
  ⟨_, (eq_zero_or_eq_succ_pred _).resolve_left H⟩

def discriminate {B : Sort u} {n : ℕ} (H1 : n = 0 → B) (H2 : ∀ m, n = succ m → B) : B :=
  by 
    induction' h : n with  <;> [exact H1 h, exact H2 _ h]

theorem one_succ_zero : 1 = succ 0 :=
  rfl

theorem pred_inj : ∀ {a b : Nat}, 0 < a → 0 < b → Nat.pred a = Nat.pred b → a = b
| succ a, succ b, ha, hb, h =>
  have  : a = b := h 
  by 
    rw [this]
| succ a, 0, ha, hb, h => absurd hb (lt_irreflₓ _)
| 0, succ b, ha, hb, h => absurd ha (lt_irreflₓ _)
| 0, 0, ha, hb, h => rfl

/-! subtraction

Many lemmas are proven more generally in mathlib `algebra/order/sub` -/


@[simp]
protected theorem zero_sub : ∀ a : ℕ, 0 - a = 0
| 0 => rfl
| a+1 => congr_argₓ pred (zero_sub a)

theorem sub_lt_succ (a b : ℕ) : a - b < succ a :=
  lt_succ_of_le (a.sub_le b)

protected theorem sub_le_sub_right {n m : ℕ} (h : n ≤ m) : ∀ k, n - k ≤ m - k
| 0 => h
| succ z => pred_le_pred (sub_le_sub_right z)

@[simp]
protected theorem sub_zero (n : ℕ) : n - 0 = n :=
  rfl

theorem sub_succ (n m : ℕ) : n - succ m = pred (n - m) :=
  rfl

theorem succ_sub_succ (n m : ℕ) : succ n - succ m = n - m :=
  succ_sub_succ_eq_sub n m

protected theorem sub_self : ∀ n : ℕ, n - n = 0
| 0 =>
  by 
    rw [Nat.sub_zero]
| succ n =>
  by 
    rw [succ_sub_succ, sub_self n]

@[ematch_lhs]
protected theorem add_sub_add_right : ∀ n k m : ℕ, ((n+k) - m+k) = n - m
| n, 0, m =>
  by 
    rw [Nat.add_zero, Nat.add_zero]
| n, succ k, m =>
  by 
    rw [add_succ, add_succ, succ_sub_succ, add_sub_add_right n k m]

@[ematch_lhs]
protected theorem add_sub_add_left (k n m : ℕ) : ((k+n) - k+m) = n - m :=
  by 
    rw [Nat.add_comm k n, Nat.add_comm k m, Nat.add_sub_add_right]

@[ematch_lhs]
protected theorem add_sub_cancel (n m : ℕ) : (n+m) - m = n :=
  suffices ((n+m) - 0+m) = n from
    by 
      rwa [Nat.zero_add] at this 
  by 
    rw [Nat.add_sub_add_right, Nat.sub_zero]

@[ematch_lhs]
protected theorem add_sub_cancel_left (n m : ℕ) : (n+m) - n = m :=
  show ((n+m) - n+0) = m from
    by 
      rw [Nat.add_sub_add_left, Nat.sub_zero]

protected theorem sub_sub : ∀ n m k : ℕ, n - m - k = n - m+k
| n, m, 0 =>
  by 
    rw [Nat.add_zero, Nat.sub_zero]
| n, m, succ k =>
  by 
    rw [add_succ, Nat.sub_succ, Nat.sub_succ, sub_sub n m k]

protected theorem le_of_le_of_sub_le_sub_right {n m k : ℕ} (h₀ : k ≤ m) (h₁ : n - k ≤ m - k) : n ≤ m :=
  by 
    revert k m 
    induction' n with n <;> intro k m h₀ h₁
    ·
      exact m.zero_le
    ·
      cases' k with k
      ·
        apply h₁ 
      cases' m with m
      ·
        cases not_succ_le_zero _ h₀
      ·
        simp [succ_sub_succ] at h₁ 
        apply succ_le_succ 
        apply n_ih _ h₁ 
        apply le_of_succ_le_succ h₀

protected theorem sub_le_sub_right_iff (n m k : ℕ) (h : k ≤ m) : n - k ≤ m - k ↔ n ≤ m :=
  ⟨Nat.le_of_le_of_sub_le_sub_rightₓ h, fun h => Nat.sub_le_sub_rightₓ h k⟩

protected theorem sub_self_add (n m : ℕ) : (n - n+m) = 0 :=
  show ((n+0) - n+m) = 0 from
    by 
      rw [Nat.add_sub_add_left, Nat.zero_sub]

protected theorem add_le_to_le_sub (x : ℕ) {y k : ℕ} (h : k ≤ y) : (x+k) ≤ y ↔ x ≤ y - k :=
  by 
    rw [←Nat.add_sub_cancel x k, Nat.sub_le_sub_right_iffₓ _ _ _ h, Nat.add_sub_cancel]

protected theorem sub_lt_of_pos_le (a b : ℕ) (h₀ : 0 < a) (h₁ : a ≤ b) : b - a < b :=
  by 
    apply Nat.sub_ltₓ _ h₀ 
    apply lt_of_lt_of_leₓ h₀ h₁

protected theorem sub_one (n : ℕ) : n - 1 = pred n :=
  rfl

theorem succ_sub_one (n : ℕ) : succ n - 1 = n :=
  rfl

theorem succ_pred_eq_of_pos : ∀ {n : ℕ}, 0 < n → succ (pred n) = n
| 0, h => absurd h (lt_irreflₓ 0)
| succ k, h => rfl

protected theorem sub_eq_zero_of_le {n m : ℕ} (h : n ≤ m) : n - m = 0 :=
  Exists.elim (Nat.Le.dest h)
    fun k =>
      fun hk : (n+k) = m =>
        by 
          rw [←hk, Nat.sub_self_add]

protected theorem le_of_sub_eq_zero : ∀ {n m : ℕ}, n - m = 0 → n ≤ m
| n, 0, H =>
  by 
    rw [Nat.sub_zero] at H 
    simp [H]
| 0, m+1, H => (m+1).zero_le
| n+1, m+1, H =>
  Nat.add_le_add_rightₓ
    (le_of_sub_eq_zero
      (by 
        simp [Nat.add_sub_add_right] at H 
        exact H))
    _

protected theorem sub_eq_zero_iff_le {n m : ℕ} : n - m = 0 ↔ n ≤ m :=
  ⟨Nat.le_of_sub_eq_zeroₓ, Nat.sub_eq_zero_of_leₓ⟩

protected theorem add_sub_of_le {n m : ℕ} (h : n ≤ m) : (n+m - n) = m :=
  Exists.elim (Nat.Le.dest h)
    fun k =>
      fun hk : (n+k) = m =>
        by 
          rw [←hk, Nat.add_sub_cancel_left]

protected theorem sub_add_cancel {n m : ℕ} (h : m ≤ n) : ((n - m)+m) = n :=
  by 
    rw [Nat.add_comm, Nat.add_sub_of_leₓ h]

protected theorem add_sub_assoc {m k : ℕ} (h : k ≤ m) (n : ℕ) : (n+m) - k = n+m - k :=
  Exists.elim (Nat.Le.dest h)
    fun l =>
      fun hl : (k+l) = m =>
        by 
          rw [←hl, Nat.add_sub_cancel_left, Nat.add_comm k, ←Nat.add_assoc, Nat.add_sub_cancel]

protected theorem sub_eq_iff_eq_add {a b c : ℕ} (ab : b ≤ a) : a - b = c ↔ a = c+b :=
  ⟨fun c_eq =>
      by 
        rw [c_eq.symm, Nat.sub_add_cancelₓ ab],
    fun a_eq =>
      by 
        rw [a_eq, Nat.add_sub_cancel]⟩

protected theorem lt_of_sub_eq_succ {m n l : ℕ} (H : m - n = Nat.succ l) : n < m :=
  not_leₓ.1
    fun H' : n ≥ m =>
      by 
        simp [Nat.sub_eq_zero_of_leₓ H'] at H 
        contradiction

protected theorem sub_le_sub_left {n m : ℕ} k (h : n ≤ m) : k - m ≤ k - n :=
  by 
    induction h <;> [rfl, exact le_transₓ (pred_le _) h_ih]

theorem succ_sub_sub_succ (n m k : ℕ) : succ n - m - succ k = n - m - k :=
  by 
    rw [Nat.sub_sub, Nat.sub_sub, add_succ, succ_sub_succ]

protected theorem sub.right_comm (m n k : ℕ) : m - n - k = m - k - n :=
  by 
    rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]

theorem succ_sub {m n : ℕ} (h : n ≤ m) : succ m - n = succ (m - n) :=
  Exists.elim (Nat.Le.dest h)
    fun k =>
      fun hk : (n+k) = m =>
        by 
          rw [←hk, Nat.add_sub_cancel_left, ←add_succ, Nat.add_sub_cancel_left]

protected theorem sub_pos_of_lt {m n : ℕ} (h : m < n) : 0 < n - m :=
  have  : (0+m) < (n - m)+m :=
    by 
      rw [Nat.zero_add, Nat.sub_add_cancelₓ (le_of_ltₓ h)]
      exact h 
  Nat.lt_of_add_lt_add_rightₓ this

protected theorem sub_sub_self {n m : ℕ} (h : m ≤ n) : n - (n - m) = m :=
  (Nat.sub_eq_iff_eq_addₓ (Nat.sub_leₓ _ _)).2 (Nat.add_sub_of_leₓ h).symm

protected theorem sub_add_comm {n m k : ℕ} (h : k ≤ n) : (n+m) - k = (n - k)+m :=
  (Nat.sub_eq_iff_eq_addₓ (Nat.le_transₓ h (Nat.le_add_rightₓ _ _))).2
    (by 
      rwa [Nat.add_right_comm, Nat.sub_add_cancelₓ])

theorem sub_one_sub_lt {n i} (h : i < n) : n - 1 - i < n :=
  by 
    rw [Nat.sub_sub]
    apply Nat.sub_ltₓ 
    apply lt_of_lt_of_leₓ (Nat.zero_lt_succₓ _) h 
    rw [Nat.add_comm]
    apply Nat.zero_lt_succₓ

theorem mul_pred_left : ∀ n m : ℕ, (pred n*m) = (n*m) - m
| 0, m =>
  by 
    simp [Nat.zero_sub, pred_zero, Nat.zero_mul]
| succ n, m =>
  by 
    rw [pred_succ, succ_mul, Nat.add_sub_cancel]

theorem mul_pred_right (n m : ℕ) : (n*pred m) = (n*m) - n :=
  by 
    rw [Nat.mul_comm, mul_pred_left, Nat.mul_comm]

protected theorem mul_sub_right_distrib : ∀ n m k : ℕ, ((n - m)*k) = (n*k) - m*k
| n, 0, k =>
  by 
    simp [Nat.sub_zero, Nat.zero_mul]
| n, succ m, k =>
  by 
    rw [Nat.sub_succ, mul_pred_left, mul_sub_right_distrib, succ_mul, Nat.sub_sub]

protected theorem mul_sub_left_distrib (n m k : ℕ) : (n*m - k) = (n*m) - n*k :=
  by 
    rw [Nat.mul_comm, Nat.mul_sub_right_distrib, Nat.mul_comm m n, Nat.mul_comm n k]

protected theorem mul_self_sub_mul_self_eq (a b : Nat) : ((a*a) - b*b) = (a+b)*a - b :=
  by 
    rw [Nat.mul_sub_left_distrib, Nat.right_distrib, Nat.right_distrib, Nat.mul_comm b a, Nat.add_comm (a*a) (a*b),
      Nat.add_sub_add_left]

theorem succ_mul_succ_eq (a b : Nat) : (succ a*succ b) = (((a*b)+a)+b)+1 :=
  by 
    rw [←add_one, ←add_one]
    simp [Nat.right_distrib, Nat.left_distrib, Nat.add_left_comm, Nat.mul_one, Nat.one_mul, Nat.add_assoc]

/-! min -/


protected theorem zero_min (a : ℕ) : min 0 a = 0 :=
  min_eq_leftₓ a.zero_le

protected theorem min_zero (a : ℕ) : min a 0 = 0 :=
  min_eq_rightₓ a.zero_le

theorem min_succ_succ (x y : ℕ) : min (succ x) (succ y) = succ (min x y) :=
  have f : x ≤ y → min (succ x) (succ y) = succ (min x y) :=
    fun p =>
      calc min (succ x) (succ y) = succ x := if_pos (succ_le_succ p)
        _ = succ (min x y) := congr_argₓ succ (Eq.symm (if_pos p))
        
  have g : ¬x ≤ y → min (succ x) (succ y) = succ (min x y) :=
    fun p =>
      calc min (succ x) (succ y) = succ y := if_neg fun eq => p (pred_le_pred Eq)
        _ = succ (min x y) := congr_argₓ succ (Eq.symm (if_neg p))
        
  Decidable.byCases f g

theorem sub_eq_sub_min (n m : ℕ) : n - m = n - min n m :=
  if h : n ≥ m then
    by 
      rw [min_eq_rightₓ h]
  else
    by 
      rw [Nat.sub_eq_zero_of_leₓ (le_of_not_geₓ h), min_eq_leftₓ (le_of_not_geₓ h), Nat.sub_self]

@[simp]
protected theorem sub_add_min_cancel (n m : ℕ) : ((n - m)+min n m) = n :=
  by 
    rw [sub_eq_sub_min, Nat.sub_add_cancelₓ (min_le_leftₓ n m)]

/-! induction principles -/


def two_step_induction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
  (H3 : ∀ n : ℕ IH1 : P n IH2 : P (succ n), P (succ (succ n))) : ∀ a : ℕ, P a
| 0 => H1
| 1 => H2
| succ (succ n) => H3 _ (two_step_induction _) (two_step_induction _)

def sub_induction {P : ℕ → ℕ → Sort u} (H1 : ∀ m, P 0 m) (H2 : ∀ n, P (succ n) 0)
  (H3 : ∀ n m, P n m → P (succ n) (succ m)) : ∀ n m : ℕ, P n m
| 0, m => H1 _
| succ n, 0 => H2 _
| succ n, succ m => H3 _ _ (sub_induction n m)

protected def strong_rec_on {p : Nat → Sort u} (n : Nat) (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
  suffices ∀ n m, m < n → p m from this (succ n) n (lt_succ_self _)
  by 
    intro n 
    induction' n with n ih
    ·
      intro m h₁ 
      exact absurd h₁ m.not_lt_zero
    ·
      intro m h₁ 
      apply Or.byCases (Decidable.lt_or_eq_of_leₓ (le_of_lt_succ h₁))
      ·
        intros 
        apply ih 
        assumption
      ·
        intros 
        subst m 
        apply h _ ih

protected theorem strong_induction_on {p : Nat → Prop} (n : Nat) (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
  Nat.strongRecOn n h

protected theorem case_strong_induction_on {p : Nat → Prop} (a : Nat) (hz : p 0)
  (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
  Nat.strong_induction_onₓ a$
    fun n =>
      match n with 
      | 0 => fun _ => hz
      | n+1 => fun h₁ => hi n fun m h₂ => h₁ _ (lt_succ_of_le h₂)

/-! mod -/


private theorem mod_core_congr {x y f1 f2} (h1 : x ≤ f1) (h2 : x ≤ f2) : Nat.modCore y f1 x = Nat.modCore y f2 x :=
  by 
    cases y
    ·
      cases f1 <;> cases f2 <;> rfl 
    induction' f1 with f1 ih generalizing x f2
    ·
      cases h1 
      cases f2 <;> rfl 
    cases x
    ·
      cases f1 <;> cases f2 <;> rfl 
    cases f2
    ·
      cases h2 
    refine' if_congr Iff.rfl _ rfl 
    simp only [succ_sub_succ]
    exact ih (le_transₓ (Nat.sub_leₓ _ _) (le_of_succ_le_succ h1)) (le_transₓ (Nat.sub_leₓ _ _) (le_of_succ_le_succ h2))

theorem mod_def (x y : Nat) : x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x :=
  by 
    cases x
    ·
      cases y <;> rfl 
    cases y
    ·
      rfl 
    refine' if_congr Iff.rfl (mod_core_congr _ _) rfl <;> simp [Nat.sub_leₓ]

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem mod_zero (a : nat) : «expr = »(«expr % »(a, 0), a) :=
begin
  rw [expr mod_def] [],
  have [ident h] [":", expr «expr¬ »(«expr ∧ »(«expr < »(0, 0), «expr ≤ »(0, a)))] [],
  simp [] [] [] ["[", expr lt_irrefl, "]"] [] [],
  simp [] [] [] ["[", expr if_neg, ",", expr h, "]"] [] []
end

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mod_eq_of_lt {a b : nat} (h : «expr < »(a, b)) : «expr = »(«expr % »(a, b), a) :=
begin
  rw [expr mod_def] [],
  have [ident h'] [":", expr «expr¬ »(«expr ∧ »(«expr < »(0, b), «expr ≤ »(b, a)))] [],
  simp [] [] [] ["[", expr not_le_of_gt h, "]"] [] [],
  simp [] [] [] ["[", expr if_neg, ",", expr h', "]"] [] []
end

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem zero_mod (b : nat) : «expr = »(«expr % »(0, b), 0) :=
begin
  rw [expr mod_def] [],
  have [ident h] [":", expr «expr¬ »(«expr ∧ »(«expr < »(0, b), «expr ≤ »(b, 0)))] [],
  { intro [ident hn],
    cases [expr hn] ["with", ident l, ident r],
    exact [expr absurd (lt_of_lt_of_le l r) (lt_irrefl 0)] },
  simp [] [] [] ["[", expr if_neg, ",", expr h, "]"] [] []
end

theorem mod_eq_sub_mod {a b : Nat} (h : b ≤ a) : a % b = (a - b) % b :=
  Or.elim b.eq_zero_or_pos
    (fun b0 =>
      by 
        rw [b0, Nat.sub_zero])
    fun h₂ =>
      by 
        rw [mod_def, if_pos (And.intro h₂ h)]

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mod_lt (x : nat) {y : nat} (h : «expr < »(0, y)) : «expr < »(«expr % »(x, y), y) :=
begin
  induction [expr x] ["using", ident nat.case_strong_induction_on] ["with", ident x, ident ih] [],
  { rw [expr zero_mod] [],
    assumption },
  { by_cases [expr h₁, ":", expr «expr < »(succ x, y)],
    { rwa ["[", expr mod_eq_of_lt h₁, "]"] [] },
    { have [ident h₁] [":", expr «expr = »(«expr % »(succ x, y), «expr % »(«expr - »(succ x, y), y))] [":=", expr mod_eq_sub_mod (not_lt.1 h₁)],
      have [] [":", expr «expr ≤ »(«expr - »(succ x, y), x)] [":=", expr le_of_lt_succ (nat.sub_lt (succ_pos x) h)],
      have [ident h₂] [":", expr «expr < »(«expr % »(«expr - »(succ x, y), y), y)] [":=", expr ih _ this],
      rwa ["[", "<-", expr h₁, "]"] ["at", ident h₂] } }
end

@[simp]
theorem mod_self (n : Nat) : n % n = 0 :=
  by 
    rw [mod_eq_sub_mod (le_reflₓ _), Nat.sub_self, zero_mod]

@[simp]
theorem mod_one (n : ℕ) : n % 1 = 0 :=
  have  : n % 1 < 1 := (mod_lt n) (succ_pos 0)
  Nat.eq_zero_of_le_zeroₓ (le_of_lt_succ this)

theorem mod_two_eq_zero_or_one (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 :=
  match n % 2,
    @Nat.mod_ltₓ n 2
      (by 
        decide) with
    
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr rfl
  | k+2, h =>
    absurd h
      (by 
        decide)

theorem mod_le (x y : ℕ) : x % y ≤ x :=
  Or.elim (lt_or_leₓ x y)
    (fun xlty =>
      by 
        rw [mod_eq_of_lt xlty] <;> rfl)
    fun ylex =>
      Or.elim y.eq_zero_or_pos
        (fun y0 =>
          by 
            rw [y0, mod_zero] <;> rfl)
        fun ypos => le_transₓ (le_of_ltₓ (mod_lt _ ypos)) ylex

@[simp]
theorem add_mod_right (x z : ℕ) : (x+z) % z = x % z :=
  by 
    rw [mod_eq_sub_mod (Nat.le_add_leftₓ _ _), Nat.add_sub_cancel]

@[simp]
theorem add_mod_left (x z : ℕ) : (x+z) % x = z % x :=
  by 
    rw [Nat.add_comm, add_mod_right]

@[simp]
theorem add_mul_mod_self_left (x y z : ℕ) : (x+y*z) % y = x % y :=
  by 
    induction' z with z ih 
    rw [Nat.mul_zero, Nat.add_zero]
    rw [mul_succ, ←Nat.add_assoc, add_mod_right, ih]

@[simp]
theorem add_mul_mod_self_right (x y z : ℕ) : (x+y*z) % z = x % z :=
  by 
    rw [Nat.mul_comm, add_mul_mod_self_left]

@[simp]
theorem mul_mod_right (m n : ℕ) : (m*n) % m = 0 :=
  by 
    rw [←Nat.zero_add (m*n), add_mul_mod_self_left, zero_mod]

@[simp]
theorem mul_mod_left (m n : ℕ) : (m*n) % n = 0 :=
  by 
    rw [Nat.mul_comm, mul_mod_right]

theorem mul_mod_mul_left (z x y : ℕ) : ((z*x) % z*y) = z*x % y :=
  if y0 : y = 0 then
    by 
      rw [y0, Nat.mul_zero, mod_zero, mod_zero]
  else
    if z0 : z = 0 then
      by 
        rw [z0, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, mod_zero]
    else
      x.strong_induction_on$
        fun n IH =>
          have y0 : y > 0 := Nat.pos_of_ne_zeroₓ y0 
          have z0 : z > 0 := Nat.pos_of_ne_zeroₓ z0 
          Or.elim (le_or_ltₓ y n)
            (fun yn =>
              by 
                rw [mod_eq_sub_mod yn, mod_eq_sub_mod (Nat.mul_le_mul_leftₓ z yn), ←Nat.mul_sub_left_distrib] <;>
                  exact IH _ (Nat.sub_ltₓ (lt_of_lt_of_leₓ y0 yn) y0))
            fun yn =>
              by 
                rw [mod_eq_of_lt yn, mod_eq_of_lt (Nat.mul_lt_mul_of_pos_leftₓ yn z0)]

theorem mul_mod_mul_right (z x y : ℕ) : ((x*z) % y*z) = (x % y)*z :=
  by 
    rw [Nat.mul_comm x z, Nat.mul_comm y z, Nat.mul_comm (x % y) z] <;> apply mul_mod_mul_left

theorem cond_to_bool_mod_two (x : ℕ) [d : Decidable (x % 2 = 1)] : cond (@to_bool (x % 2 = 1) d) 1 0 = x % 2 :=
  by 
    byCases' h : x % 2 = 1
    ·
      simp 
    ·
      cases mod_two_eq_zero_or_one x <;> simp [Nat.zero_ne_one]

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sub_mul_mod
(x k n : exprℕ())
(h₁ : «expr ≤ »(«expr * »(n, k), x)) : «expr = »(«expr % »(«expr - »(x, «expr * »(n, k)), n), «expr % »(x, n)) :=
begin
  induction [expr k] [] ["with", ident k] [],
  { rw ["[", expr nat.mul_zero, ",", expr nat.sub_zero, "]"] [] },
  { have [ident h₂] [":", expr «expr ≤ »(«expr * »(n, k), x)] [],
    { rw ["[", expr mul_succ, "]"] ["at", ident h₁],
      apply [expr nat.le_trans _ h₁],
      apply [expr nat.le_add_right _ n] },
    have [ident h₄] [":", expr «expr ≥ »(«expr - »(x, «expr * »(n, k)), n)] [],
    { apply [expr @nat.le_of_add_le_add_right «expr * »(n, k)],
      rw ["[", expr nat.sub_add_cancel h₂, "]"] [],
      simp [] [] [] ["[", expr mul_succ, ",", expr nat.add_comm, "]"] [] ["at", ident h₁],
      simp [] [] [] ["[", expr h₁, "]"] [] [] },
    rw ["[", expr mul_succ, ",", "<-", expr nat.sub_sub, ",", "<-", expr mod_eq_sub_mod h₄, ",", expr k_ih h₂, "]"] [] }
end

/-! div -/


private theorem div_core_congr {x y f1 f2} (h1 : x ≤ f1) (h2 : x ≤ f2) : Nat.divCore y f1 x = Nat.divCore y f2 x :=
  by 
    cases y
    ·
      cases f1 <;> cases f2 <;> rfl 
    induction' f1 with f1 ih generalizing x f2
    ·
      cases h1 
      cases f2 <;> rfl 
    cases x
    ·
      cases f1 <;> cases f2 <;> rfl 
    cases f2
    ·
      cases h2 
    refine' if_congr Iff.rfl _ rfl 
    simp only [succ_sub_succ]
    refine' congr_argₓ (·+1) _ 
    exact ih (le_transₓ (Nat.sub_leₓ _ _) (le_of_succ_le_succ h1)) (le_transₓ (Nat.sub_leₓ _ _) (le_of_succ_le_succ h2))

theorem div_def (x y : Nat) : x / y = if 0 < y ∧ y ≤ x then ((x - y) / y)+1 else 0 :=
  by 
    cases x
    ·
      cases y <;> rfl 
    cases y
    ·
      rfl 
    refine' if_congr Iff.rfl (congr_argₓ (·+1) _) rfl 
    refine' div_core_congr _ _ <;> simp [Nat.sub_leₓ]

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mod_add_div (m k : exprℕ()) : «expr = »(«expr + »(«expr % »(m, k), «expr * »(k, «expr / »(m, k))), m) :=
begin
  apply [expr nat.strong_induction_on m],
  clear [ident m],
  intros [ident m, ident IH],
  cases [expr decidable.em «expr ∧ »(«expr < »(0, k), «expr ≤ »(k, m))] ["with", ident h, ident h'],
  { have [ident h'] [":", expr «expr < »(«expr - »(m, k), m)] [],
    { apply [expr nat.sub_lt _ h.left],
      apply [expr lt_of_lt_of_le h.left h.right] },
    rw ["[", expr div_def, ",", expr mod_def, ",", expr if_pos h, ",", expr if_pos h, "]"] [],
    simp [] [] [] ["[", expr nat.left_distrib, ",", expr IH _ h', ",", expr nat.add_comm, ",", expr nat.add_left_comm, "]"] [] [],
    rw ["[", expr nat.add_comm, ",", "<-", expr nat.add_sub_assoc h.right, ",", expr nat.mul_one, ",", expr nat.add_sub_cancel_left, "]"] [] },
  { rw ["[", expr div_def, ",", expr mod_def, ",", expr if_neg h', ",", expr if_neg h', ",", expr nat.mul_zero, ",", expr nat.add_zero, "]"] [] }
end

@[simp]
protected theorem div_one (n : ℕ) : n / 1 = n :=
  have  : ((n % 1)+1*n / 1) = n := mod_add_div _ _ 
  by 
    rwa [mod_one, Nat.zero_add, Nat.one_mul] at this

@[simp]
protected theorem div_zero (n : ℕ) : n / 0 = 0 :=
  by 
    rw [div_def]
    simp [lt_irreflₓ]

@[simp]
protected theorem zero_div (b : ℕ) : 0 / b = 0 :=
  Eq.trans (div_def 0 b)$ if_neg (And.ndrec not_le_of_gtₓ)

protected theorem div_le_of_le_mul {m n : ℕ} : ∀ {k}, (m ≤ k*n) → m / k ≤ n
| 0, h =>
  by 
    simp [Nat.div_zeroₓ, n.zero_le]
| succ k, h =>
  suffices (succ k*m / succ k) ≤ succ k*n from Nat.le_of_mul_le_mul_leftₓ this (zero_lt_succ _)
  calc (succ k*m / succ k) ≤ (m % succ k)+succ k*m / succ k := Nat.le_add_leftₓ _ _ 
    _ = m :=
    by 
      rw [mod_add_div]
    _ ≤ succ k*n := h
    

protected theorem div_le_self : ∀ m n : ℕ, m / n ≤ m
| m, 0 =>
  by 
    simp [Nat.div_zeroₓ, m.zero_le]
| m, succ n =>
  have  : m ≤ succ n*m :=
    calc m = 1*m :=
      by 
        rw [Nat.one_mul]
      _ ≤ succ n*m := m.mul_le_mul_right (succ_le_succ n.zero_le)
      
  Nat.div_le_of_le_mulₓ this

theorem div_eq_sub_div {a b : Nat} (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = ((a - b) / b)+1 :=
  by 
    rw [div_def a, if_pos]
    split  <;> assumption

theorem div_eq_of_lt {a b : ℕ} (h₀ : a < b) : a / b = 0 :=
  by 
    rw [div_def a, if_neg]
    intro h₁ 
    apply not_le_of_gtₓ h₀ h₁.right

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_div_iff_mul_le
(x y : exprℕ())
{k : exprℕ()}
(Hk : «expr < »(0, k)) : «expr ↔ »(«expr ≤ »(x, «expr / »(y, k)), «expr ≤ »(«expr * »(x, k), y)) :=
begin
  revert [ident x],
  apply [expr nat.strong_induction_on y _],
  clear [ident y],
  intros [ident y, ident IH, ident x],
  cases [expr lt_or_le y k] ["with", ident h, ident h],
  { rw ["[", expr div_eq_of_lt h, "]"] [],
    cases [expr x] ["with", ident x],
    { simp [] [] [] ["[", expr nat.zero_mul, ",", expr y.zero_le, "]"] [] [] },
    { simp [] [] [] ["[", expr succ_mul, ",", expr not_succ_le_zero, ",", expr nat.add_comm, "]"] [] [],
      apply [expr lt_of_lt_of_le h],
      apply [expr nat.le_add_right] } },
  { rw ["[", expr div_eq_sub_div Hk h, "]"] [],
    cases [expr x] ["with", ident x],
    { simp [] [] [] ["[", expr nat.zero_mul, ",", expr nat.zero_le, "]"] [] [] },
    { have [ident Hlt] [":", expr «expr < »(«expr - »(y, k), y)] [],
      { apply [expr nat.sub_lt_of_pos_le]; assumption },
      rw ["[", "<-", expr add_one, ",", expr nat.add_le_add_iff_le_right, ",", expr IH «expr - »(y, k) Hlt x, ",", expr add_one, ",", expr succ_mul, ",", expr nat.add_le_to_le_sub _ h, "]"] [] } }
end

theorem div_lt_iff_lt_mul (x y : ℕ) {k : ℕ} (Hk : 0 < k) : x / k < y ↔ x < y*k :=
  by 
    simp [←not_leₓ]
    apply not_iff_not_of_iff 
    apply le_div_iff_mul_le _ _ Hk

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sub_mul_div
(x n p : exprℕ())
(h₁ : «expr ≤ »(«expr * »(n, p), x)) : «expr = »(«expr / »(«expr - »(x, «expr * »(n, p)), n), «expr - »(«expr / »(x, n), p)) :=
begin
  cases [expr nat.eq_zero_or_pos n] ["with", ident h₀, ident h₀],
  { rw ["[", expr h₀, ",", expr nat.div_zero, ",", expr nat.div_zero, ",", expr nat.zero_sub, "]"] [] },
  { induction [expr p] [] ["with", ident p] [],
    { rw ["[", expr nat.mul_zero, ",", expr nat.sub_zero, ",", expr nat.sub_zero, "]"] [] },
    { have [ident h₂] [":", expr «expr ≤ »(«expr * »(n, p), x)] [],
      { transitivity [],
        { apply [expr nat.mul_le_mul_left],
          apply [expr le_succ] },
        { apply [expr h₁] } },
      have [ident h₃] [":", expr «expr ≥ »(«expr - »(x, «expr * »(n, p)), n)] [],
      { apply [expr nat.le_of_add_le_add_right],
        rw ["[", expr nat.sub_add_cancel h₂, ",", expr nat.add_comm, "]"] [],
        rw ["[", expr mul_succ, "]"] ["at", ident h₁],
        apply [expr h₁] },
      rw ["[", expr sub_succ, ",", "<-", expr p_ih h₂, "]"] [],
      rw ["[", expr @div_eq_sub_div «expr - »(x, «expr * »(n, p)) _ h₀ h₃, "]"] [],
      simp [] [] [] ["[", expr add_one, ",", expr pred_succ, ",", expr mul_succ, ",", expr nat.sub_sub, "]"] [] [] } }
end

theorem div_mul_le_self : ∀ m n : ℕ, ((m / n)*n) ≤ m
| m, 0 =>
  by 
    simp [m.zero_le, Nat.zero_mul]
| m, succ n => (le_div_iff_mul_le _ _ (Nat.succ_posₓ _)).1 (le_reflₓ _)

@[simp]
theorem add_div_right (x : ℕ) {z : ℕ} (H : 0 < z) : (x+z) / z = succ (x / z) :=
  by 
    rw [div_eq_sub_div H (Nat.le_add_leftₓ _ _), Nat.add_sub_cancel]

@[simp]
theorem add_div_left (x : ℕ) {z : ℕ} (H : 0 < z) : (z+x) / z = succ (x / z) :=
  by 
    rw [Nat.add_comm, add_div_right x H]

@[simp]
theorem mul_div_right (n : ℕ) {m : ℕ} (H : 0 < m) : (m*n) / m = n :=
  by 
    induction n <;> simp [mul_succ, Nat.mul_zero]

@[simp]
theorem mul_div_left (m : ℕ) {n : ℕ} (H : 0 < n) : (m*n) / n = m :=
  by 
    rw [Nat.mul_comm, mul_div_right _ H]

protected theorem div_self {n : ℕ} (H : 0 < n) : n / n = 1 :=
  let t := add_div_right 0 H 
  by 
    rwa [Nat.zero_add, Nat.zero_divₓ] at t

theorem add_mul_div_left (x z : ℕ) {y : ℕ} (H : 0 < y) : (x+y*z) / y = (x / y)+z :=
  by 
    induction' z with z ih
    ·
      rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
    ·
      rw [mul_succ, ←Nat.add_assoc, add_div_right _ H, ih]
      rfl

theorem add_mul_div_right (x y : ℕ) {z : ℕ} (H : 0 < z) : (x+y*z) / z = (x / z)+y :=
  by 
    rw [Nat.mul_comm, add_mul_div_left _ _ H]

protected theorem mul_div_cancel (m : ℕ) {n : ℕ} (H : 0 < n) : (m*n) / n = m :=
  let t := add_mul_div_right 0 m H 
  by 
    rwa [Nat.zero_add, Nat.zero_divₓ, Nat.zero_add] at t

protected theorem mul_div_cancel_left (m : ℕ) {n : ℕ} (H : 0 < n) : (n*m) / n = m :=
  by 
    rw [Nat.mul_comm, Nat.mul_div_cancelₓ _ H]

protected theorem div_eq_of_eq_mul_left {m n k : ℕ} (H1 : 0 < n) (H2 : m = k*n) : m / n = k :=
  by 
    rw [H2, Nat.mul_div_cancelₓ _ H1]

protected theorem div_eq_of_eq_mul_right {m n k : ℕ} (H1 : 0 < n) (H2 : m = n*k) : m / n = k :=
  by 
    rw [H2, Nat.mul_div_cancel_leftₓ _ H1]

protected theorem div_eq_of_lt_le {m n k : ℕ} (lo : (k*n) ≤ m) (hi : m < succ k*n) : m / n = k :=
  have npos : 0 < n :=
    n.eq_zero_or_pos.resolve_left$
      fun hn =>
        by 
          rw [hn, Nat.mul_zero] at hi lo <;> exact absurd lo (not_le_of_gtₓ hi)
  le_antisymmₓ (le_of_lt_succ ((Nat.div_lt_iff_lt_mulₓ _ _ npos).2 hi)) ((Nat.le_div_iff_mul_leₓ _ _ npos).2 lo)

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_sub_div
(x n p : exprℕ())
(h₁ : «expr < »(x, «expr * »(n, p))) : «expr = »(«expr / »(«expr - »(«expr * »(n, p), succ x), n), «expr - »(p, succ «expr / »(x, n))) :=
begin
  have [ident npos] [":", expr «expr < »(0, n)] [":=", expr n.eq_zero_or_pos.resolve_left (λ
    n0, by rw ["[", expr n0, ",", expr nat.zero_mul, "]"] ["at", ident h₁]; exact [expr nat.not_lt_zero _ h₁])],
  apply [expr nat.div_eq_of_lt_le],
  { rw ["[", expr nat.mul_sub_right_distrib, ",", expr nat.mul_comm, "]"] [],
    apply [expr nat.sub_le_sub_left],
    exact [expr (div_lt_iff_lt_mul _ _ npos).1 (lt_succ_self _)] },
  { change [expr «expr ≤ »(succ (pred «expr - »(«expr * »(n, p), x)), «expr * »(succ (pred «expr - »(p, «expr / »(x, n))), n))] [] [],
    rw ["[", expr succ_pred_eq_of_pos (nat.sub_pos_of_lt h₁), ",", expr succ_pred_eq_of_pos (nat.sub_pos_of_lt _), "]"] [],
    { rw ["[", expr nat.mul_sub_right_distrib, ",", expr nat.mul_comm, "]"] [],
      apply [expr nat.sub_le_sub_left],
      apply [expr div_mul_le_self] },
    { apply [expr (div_lt_iff_lt_mul _ _ npos).2],
      rwa [expr nat.mul_comm] [] } }
end

protected theorem div_div_eq_div_mul (m n k : ℕ) : m / n / k = m / n*k :=
  by 
    cases' k.eq_zero_or_pos with k0 kpos
    ·
      rw [k0, Nat.mul_zero, Nat.div_zeroₓ, Nat.div_zeroₓ]
    cases' n.eq_zero_or_pos with n0 npos
    ·
      rw [n0, Nat.zero_mul, Nat.div_zeroₓ, Nat.zero_divₓ]
    apply le_antisymmₓ
    ·
      apply (le_div_iff_mul_le _ _ (Nat.mul_posₓ npos kpos)).2
      rw [Nat.mul_comm n k, ←Nat.mul_assoc]
      apply (le_div_iff_mul_le _ _ npos).1
      apply (le_div_iff_mul_le _ _ kpos).1
      rfl
    ·
      apply (le_div_iff_mul_le _ _ kpos).2
      apply (le_div_iff_mul_le _ _ npos).2
      rw [Nat.mul_assoc, Nat.mul_comm n k]
      apply (le_div_iff_mul_le _ _ (Nat.mul_posₓ kpos npos)).1
      rfl

protected theorem mul_div_mul {m : ℕ} (n k : ℕ) (H : 0 < m) : ((m*n) / m*k) = n / k :=
  by 
    rw [←Nat.div_div_eq_div_mulₓ, Nat.mul_div_cancel_leftₓ _ H]

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem div_lt_self {n m : nat} : «expr < »(0, n) → «expr < »(1, m) → «expr < »(«expr / »(n, m), n) :=
begin
  intros [ident h₁, ident h₂],
  have [ident m_pos] [":", expr «expr < »(0, m)] [],
  { apply [expr lt_trans _ h₂],
    comp_val },
  suffices [] [":", expr «expr < »(«expr * »(1, n), «expr * »(m, n))],
  { rw ["[", expr nat.one_mul, ",", expr nat.mul_comm, "]"] ["at", ident this],
    exact [expr iff.mpr (nat.div_lt_iff_lt_mul n n m_pos) this] },
  exact [expr nat.mul_lt_mul h₂ (le_refl _) h₁]
end

/-! dvd -/


protected theorem dvd_mul_right (a b : ℕ) : a ∣ a*b :=
  ⟨b, rfl⟩

protected theorem dvd_trans {a b c : ℕ} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
  match h₁, h₂ with 
  | ⟨d, (h₃ : b = a*d)⟩, ⟨e, (h₄ : c = b*e)⟩ =>
    ⟨d*e,
      show c = a*d*e by 
        simp [h₃, h₄, Nat.mul_assoc]⟩

protected theorem eq_zero_of_zero_dvd {a : ℕ} (h : 0 ∣ a) : a = 0 :=
  Exists.elim h fun c => fun H' : a = 0*c => Eq.trans H' (Nat.zero_mul c)

protected theorem dvd_add {a b c : ℕ} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b+c :=
  Exists.elim h₁
    fun d hd =>
      Exists.elim h₂
        fun e he =>
          ⟨d+e,
            by 
              simp [Nat.left_distrib, hd, he]⟩

protected theorem dvd_add_iff_right {k m n : ℕ} (h : k ∣ m) : k ∣ n ↔ k ∣ m+n :=
  ⟨Nat.dvd_add h,
    Exists.elim h$
      fun d hd =>
        match m, hd with 
        | _, rfl =>
          fun h₂ =>
            Exists.elim h₂$
              fun e he =>
                ⟨e - d,
                  by 
                    rw [Nat.mul_sub_left_distrib, ←he, Nat.add_sub_cancel_left]⟩⟩

protected theorem dvd_add_iff_left {k m n : ℕ} (h : k ∣ n) : k ∣ m ↔ k ∣ m+n :=
  by 
    rw [Nat.add_comm] <;> exact Nat.dvd_add_iff_right h

theorem dvd_sub {k m n : ℕ} (H : n ≤ m) (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
  (Nat.dvd_add_iff_left h₂).2$
    by 
      rw [Nat.sub_add_cancelₓ H] <;> exact h₁

theorem dvd_mod_iff {k m n : ℕ} (h : k ∣ n) : k ∣ m % n ↔ k ∣ m :=
  let t := @Nat.dvd_add_iff_left _ (m % n) _ (Nat.dvd_trans h (Nat.dvd_mul_right n (m / n)))
  by 
    rwa [mod_add_div] at t

theorem le_of_dvd {m n : ℕ} (h : 0 < n) : m ∣ n → m ≤ n :=
  fun ⟨k, e⟩ =>
    by 
      revert h 
      rw [e]
      refine' k.cases_on _ _ 
      exact fun hn => absurd hn (lt_irreflₓ _)
      exact
        fun k _ =>
          let t := m.mul_le_mul_left (succ_pos k)
          by 
            rwa [Nat.mul_one] at t

theorem dvd_antisymm : ∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
| m, 0, h₁, h₂ => Nat.eq_zero_of_zero_dvd h₂
| 0, n, h₁, h₂ => (Nat.eq_zero_of_zero_dvd h₁).symm
| succ m, succ n, h₁, h₂ => le_antisymmₓ (le_of_dvd (succ_pos _) h₁) (le_of_dvd (succ_pos _) h₂)

theorem pos_of_dvd_of_pos {m n : ℕ} (H1 : m ∣ n) (H2 : 0 < n) : 0 < m :=
  Nat.pos_of_ne_zeroₓ$
    fun m0 =>
      by 
        rw [m0] at H1 <;> rw [Nat.eq_zero_of_zero_dvd H1] at H2 <;> exact lt_irreflₓ _ H2

theorem eq_one_of_dvd_one {n : ℕ} (H : n ∣ 1) : n = 1 :=
  le_antisymmₓ
    (le_of_dvd
      (by 
        decide)
      H)
    (pos_of_dvd_of_pos H
      (by 
        decide))

-- error in Init.Data.Nat.Lemmas: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dvd_of_mod_eq_zero {m n : exprℕ()} (H : «expr = »(«expr % »(n, m), 0)) : «expr ∣ »(m, n) :=
⟨«expr / »(n, m), by { have [ident t] [] [":=", expr (mod_add_div n m).symm],
   rwa ["[", expr H, ",", expr nat.zero_add, "]"] ["at", ident t] }⟩

theorem mod_eq_zero_of_dvd {m n : ℕ} (H : m ∣ n) : n % m = 0 :=
  Exists.elim H
    fun z H1 =>
      by 
        rw [H1, mul_mod_right]

theorem dvd_iff_mod_eq_zero (m n : ℕ) : m ∣ n ↔ n % m = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

instance decidable_dvd : @DecidableRel ℕ (· ∣ ·) :=
  fun m n =>
    decidableOfDecidableOfIff
      (by 
        infer_instance)
      (dvd_iff_mod_eq_zero _ _).symm

protected theorem mul_div_cancel' {m n : ℕ} (H : n ∣ m) : (n*m / n) = m :=
  let t := mod_add_div m n 
  by 
    rwa [mod_eq_zero_of_dvd H, Nat.zero_add] at t

protected theorem div_mul_cancel {m n : ℕ} (H : n ∣ m) : ((m / n)*n) = m :=
  by 
    rw [Nat.mul_comm, Nat.mul_div_cancel'ₓ H]

protected theorem mul_div_assoc (m : ℕ) {n k : ℕ} (H : k ∣ n) : (m*n) / k = m*n / k :=
  Or.elim k.eq_zero_or_pos
    (fun h =>
      by 
        rw [h, Nat.div_zeroₓ, Nat.div_zeroₓ, Nat.mul_zero])
    fun h =>
      have  : (m*n) / k = (m*(n / k)*k) / k :=
        by 
          rw [Nat.div_mul_cancelₓ H]
      by 
        rw [this, ←Nat.mul_assoc, Nat.mul_div_cancelₓ _ h]

theorem dvd_of_mul_dvd_mul_left {m n k : ℕ} (kpos : 0 < k) (H : (k*m) ∣ k*n) : m ∣ n :=
  Exists.elim H
    fun l H1 =>
      by 
        rw [Nat.mul_assoc] at H1 <;> exact ⟨_, Nat.eq_of_mul_eq_mul_leftₓ kpos H1⟩

theorem dvd_of_mul_dvd_mul_right {m n k : ℕ} (kpos : 0 < k) (H : (m*k) ∣ n*k) : m ∣ n :=
  by 
    rw [Nat.mul_comm m k, Nat.mul_comm n k] at H <;> exact dvd_of_mul_dvd_mul_left kpos H

/-! iterate -/


def iterate {α : Sort u} (op : α → α) : ℕ → α → α
| 0, a => a
| succ k, a => iterate k (op a)

notation f "^[" n "]" => iterate f n

/-! find -/


section Find

parameter {p : ℕ → Prop}

private def lbp (m n : ℕ) : Prop :=
  (m = n+1) ∧ ∀ k _ : k ≤ n, ¬p k

parameter [DecidablePred p](H : ∃ n, p n)

private def wf_lbp : WellFounded lbp :=
  ⟨let ⟨n, pn⟩ := H 
    suffices ∀ m k, (n ≤ k+m) → Acc lbp k from fun a => this _ _ (Nat.le_add_leftₓ _ _)
    fun m =>
      Nat.recOn m
        (fun k kn =>
          ⟨_,
            fun y r =>
              match y, r with 
              | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
        fun m IH k kn =>
          ⟨_,
            fun y r =>
              match y, r with 
              | _, ⟨rfl, a⟩ =>
                IH _
                  (by 
                    rw [Nat.add_right_comm] <;> exact kn)⟩⟩

protected def find_x : { n // p n ∧ ∀ m _ : m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n _ : n < k, ¬p n) → { n // p n ∧ ∀ m _ : m < n, ¬p m }) lbp wf_lbp
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩ else
        have  : ∀ n _ : n ≤ m, ¬p n :=
          fun n h =>
            Or.elim (Decidable.lt_or_eq_of_leₓ h) (al n)
              fun e =>
                by 
                  rw [e] <;> exact pm 
        IH _ ⟨rfl, this⟩ fun n h => this n$ Nat.le_of_succ_le_succₓ h)
    0 fun n h => absurd h (Nat.not_lt_zeroₓ _)

/--
If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `nat.find hp` is the
smallest natural number satisfying `p`. Note that `nat.find` is protected,
meaning that you can't just write `find`, even if the `nat` namespace is open.

The API for `nat.find` is:

* `nat.find_spec` is the proof that `nat.find hp` satisfies `p`.
* `nat.find_min` is the proof that if `m < nat.find hp` then `m` does not satisfy `p`.
* `nat.find_min'` is the proof that if `m` does satisfy `p` then `nat.find hp ≤ m`.
-/
protected def find : ℕ :=
  Nat.findX.1

protected theorem find_spec : p Nat.findₓ :=
  Nat.findX.2.left

protected theorem find_min : ∀ {m : ℕ}, m < Nat.findₓ → ¬p m :=
  Nat.findX.2.right

protected theorem find_min' {m : ℕ} (h : p m) : Nat.findₓ ≤ m :=
  le_of_not_ltₓ fun l => find_min l h

end Find

end Nat

