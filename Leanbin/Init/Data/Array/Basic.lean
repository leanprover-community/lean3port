/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Leanbin.Init.Data.Nat.Default
import Leanbin.Init.Data.Bool.Default
import Leanbin.Init.IteSimp

universe u v w

/-- In the VM, d_array is implemented as a persistent array. -/
structure DArray (n : Nat) (α : Finₓ n → Type u) where
  data : ∀ i : Finₓ n, α i

namespace DArray

variable {n : Nat} {α : Finₓ n → Type u} {α' : Finₓ n → Type v} {β : Type w}

/-- The empty array. -/
def nil {α} : DArray 0 α where
  data := fun ⟨x, h⟩ => absurd h (Nat.not_lt_zeroₓ x)

/-- `read a i` reads the `i`th member of `a`. Has builtin VM implementation. -/
def read (a : DArray n α) (i : Finₓ n) : α i :=
  a.data i

/-- `write a i v` sets the `i`th member of `a` to be `v`. Has builtin VM implementation. -/
def write (a : DArray n α) (i : Finₓ n) (v : α i) : DArray n α where
  data := fun j => if h : i = j then Eq.recOnₓ h v else a.read j

def iterateAux (a : DArray n α) (f : ∀ i : Finₓ n, α i → β → β) : ∀ i : Nat, i ≤ n → β → β
  | 0, h, b => b
  | j + 1, h, b =>
    let i : Finₓ n := ⟨j, h⟩
    f i (a.read i) (iterate_aux j (le_of_ltₓ h) b)

/-- Fold over the elements of the given array in ascending order. Has builtin VM implementation. -/
def iterate (a : DArray n α) (b : β) (f : ∀ i : Finₓ n, α i → β → β) : β :=
  iterateAux a f n (le_reflₓ _) b

/-- Map the array. Has builtin VM implementation. -/
def foreach (a : DArray n α) (f : ∀ i : Finₓ n, α i → α' i) : DArray n α' :=
  ⟨fun i => f _ (a.read i)⟩

def map (f : ∀ i : Finₓ n, α i → α' i) (a : DArray n α) : DArray n α' :=
  foreach a f

def map₂ {α'' : Finₓ n → Type w} (f : ∀ i : Finₓ n, α i → α' i → α'' i) (a : DArray n α) (b : DArray n α') :
    DArray n α'' :=
  foreach b fun i => f i (a.read i)

def foldl (a : DArray n α) (b : β) (f : ∀ i : Finₓ n, α i → β → β) : β :=
  iterate a b f

def revIterateAux (a : DArray n α) (f : ∀ i : Finₓ n, α i → β → β) : ∀ i : Nat, i ≤ n → β → β
  | 0, h, b => b
  | j + 1, h, b =>
    let i : Finₓ n := ⟨j, h⟩
    rev_iterate_aux j (le_of_ltₓ h) (f i (a.read i) b)

def revIterate (a : DArray n α) (b : β) (f : ∀ i : Finₓ n, α i → β → β) : β :=
  revIterateAux a f n (le_reflₓ _) b

@[simp]
theorem read_write (a : DArray n α) (i : Finₓ n) (v : α i) : read (write a i v) i = v := by
  simp [read, write]

@[simp]
theorem read_write_of_ne (a : DArray n α) {i j : Finₓ n} (v : α i) : i ≠ j → read (write a i v) j = read a j := by
  intro h <;> simp [read, write, h]

protected theorem ext {a b : DArray n α} (h : ∀ i, read a i = read b i) : a = b := by
  cases a <;> cases b <;> congr <;> exact funext h

protected theorem ext' {a b : DArray n α} (h : ∀ i : Nat h : i < n, read a ⟨i, h⟩ = read b ⟨i, h⟩) : a = b := by
  cases a
  cases b
  congr
  funext i
  cases i
  apply h

protected def beqAux [∀ i, DecidableEq (α i)] (a b : DArray n α) : ∀ i : Nat, i ≤ n → Bool
  | 0, h => true
  | i + 1, h => if a.read ⟨i, h⟩ = b.read ⟨i, h⟩ then beq_aux i (le_of_ltₓ h) else false

/-- Boolean element-wise equality check. -/
protected def beq [∀ i, DecidableEq (α i)] (a b : DArray n α) : Bool :=
  DArray.beqAux a b n (le_reflₓ _)

theorem of_beq_aux_eq_tt [∀ i, DecidableEq (α i)] {a b : DArray n α} :
    ∀ i : Nat h : i ≤ n,
      DArray.beqAux a b i h = tt →
        ∀ j : Nat h' : j < i, a.read ⟨j, lt_of_lt_of_leₓ h' h⟩ = b.read ⟨j, lt_of_lt_of_leₓ h' h⟩
  | 0, h₁, h₂, j, h₃ => absurd h₃ (Nat.not_lt_zeroₓ _)
  | i + 1, h₁, h₂, j, h₃ => by
    have h₂' : read a ⟨i, h₁⟩ = read b ⟨i, h₁⟩ ∧ DArray.beqAux a b i _ = tt := by
      simp [DArray.beqAux] at h₂
      assumption
    have h₁' : i ≤ n := le_of_ltₓ h₁
    have ih : ∀ j : Nat h' : j < i, a.read ⟨j, lt_of_lt_of_leₓ h' h₁'⟩ = b.read ⟨j, lt_of_lt_of_leₓ h' h₁'⟩ :=
      of_beq_aux_eq_tt i h₁' h₂'.2
    by_cases' hji : j = i
    · subst hji
      exact h₂'.1
      
    · have j_lt_i : j < i := lt_of_le_of_neₓ (Nat.le_of_lt_succₓ h₃) hji
      exact ih j j_lt_i
      

theorem of_beq_eq_tt [∀ i, DecidableEq (α i)] {a b : DArray n α} : DArray.beq a b = tt → a = b := by
  unfold DArray.beq
  intro h
  have : ∀ j : Nat h : j < n, a.read ⟨j, h⟩ = b.read ⟨j, h⟩ := of_beq_aux_eq_tt n (le_reflₓ _) h
  apply DArray.ext' this

theorem of_beq_aux_eq_ff [∀ i, DecidableEq (α i)] {a b : DArray n α} :
    ∀ i : Nat h : i ≤ n,
      DArray.beqAux a b i h = ff →
        ∃ (j : Nat)(h' : j < i), a.read ⟨j, lt_of_lt_of_leₓ h' h⟩ ≠ b.read ⟨j, lt_of_lt_of_leₓ h' h⟩
  | 0, h₁, h₂ => by
    simp [DArray.beqAux] at h₂
    contradiction
  | i + 1, h₁, h₂ => by
    have h₂' : read a ⟨i, h₁⟩ ≠ read b ⟨i, h₁⟩ ∨ DArray.beqAux a b i _ = ff := by
      simp [DArray.beqAux] at h₂
      assumption
    cases' h₂' with h h
    · exists i
      exists Nat.lt_succ_selfₓ _
      exact h
      
    · have h₁' : i ≤ n := le_of_ltₓ h₁
      have ih : ∃ (j : Nat)(h' : j < i), a.read ⟨j, lt_of_lt_of_leₓ h' h₁'⟩ ≠ b.read ⟨j, lt_of_lt_of_leₓ h' h₁'⟩ :=
        of_beq_aux_eq_ff i h₁' h
      cases' ih with j ih
      cases' ih with h' ih
      exists j
      exists Nat.lt_succ_of_ltₓ h'
      exact ih
      

theorem of_beq_eq_ff [∀ i, DecidableEq (α i)] {a b : DArray n α} : DArray.beq a b = ff → a ≠ b := by
  unfold DArray.beq
  intro h hne
  have : ∃ (j : Nat)(h' : j < n), a.read ⟨j, h'⟩ ≠ b.read ⟨j, h'⟩ := of_beq_aux_eq_ff n (le_reflₓ _) h
  cases' this with j this
  cases' this with h' this
  subst hne
  contradiction

instance [∀ i, DecidableEq (α i)] : DecidableEq (DArray n α) := fun a b =>
  if h : DArray.beq a b = tt then isTrue (of_beq_eq_tt h) else isFalse (of_beq_eq_ff (eq_ff_of_not_eq_tt h))

end DArray

/-- A non-dependent array (see `d_array`). Implemented in the VM as a persistent array.  -/
def Arrayₓ (n : Nat) (α : Type u) : Type u :=
  DArray n fun _ => α

/-- `mk_array n v` creates a new array of length `n` where each element is `v`. Has builtin VM implementation. -/
def mkArray {α} n (v : α) : Arrayₓ n α where
  data := fun _ => v

namespace Arrayₓ

variable {n : Nat} {α : Type u} {β : Type v}

def nil {α} : Arrayₓ 0 α :=
  DArray.nil

@[inline]
def read (a : Arrayₓ n α) (i : Finₓ n) : α :=
  DArray.read a i

@[inline]
def write (a : Arrayₓ n α) (i : Finₓ n) (v : α) : Arrayₓ n α :=
  DArray.write a i v

/-- Fold array starting from 0, folder function includes an index argument. -/
@[inline]
def iterate (a : Arrayₓ n α) (b : β) (f : Finₓ n → α → β → β) : β :=
  DArray.iterate a b f

/-- Map each element of the given array with an index argument. -/
@[inline]
def foreach (a : Arrayₓ n α) (f : Finₓ n → α → β) : Arrayₓ n β :=
  DArray.foreach a f

@[inline]
def map₂ (f : α → α → α) (a b : Arrayₓ n α) : Arrayₓ n α :=
  foreach b fun i => f (a.read i)

@[inline]
def foldl (a : Arrayₓ n α) (b : β) (f : α → β → β) : β :=
  iterate a b fun _ => f

def revList (a : Arrayₓ n α) : List α :=
  a.foldl [] (· :: ·)

def revIterate (a : Arrayₓ n α) (b : β) (f : Finₓ n → α → β → β) : β :=
  DArray.revIterate a b f

def revFoldl (a : Arrayₓ n α) (b : β) (f : α → β → β) : β :=
  revIterate a b fun _ => f

def toList (a : Arrayₓ n α) : List α :=
  a.revFoldl [] (· :: ·)

theorem push_back_idx {j n} (h₁ : j < n + 1) (h₂ : j ≠ n) : j < n :=
  Nat.lt_of_le_and_ne (Nat.le_of_lt_succₓ h₁) h₂

/-- `push_back a v` pushes value `v` to the end of the array. Has builtin VM implementation. -/
def pushBack (a : Arrayₓ n α) (v : α) : Arrayₓ (n + 1) α where
  data := fun ⟨j, h₁⟩ => if h₂ : j = n then v else a.read ⟨j, push_back_idx h₁ h₂⟩

theorem pop_back_idx {j n} (h : j < n) : j < n + 1 :=
  Nat.Lt.step h

/-- Discard _last_ element in the array. Has builtin VM implementation. -/
def popBack (a : Arrayₓ (n + 1) α) : Arrayₓ n α where
  data := fun ⟨j, h⟩ => a.read ⟨j, pop_back_idx h⟩

/-- Auxilliary function for monadically mapping a function over an array. -/
@[inline]
def mmapCore {β : Type v} {m : Type v → Type w} [Monadₓ m] (a : Arrayₓ n α) (f : α → m β) :
    ∀, ∀ i ≤ n, ∀, m (Arrayₓ i β)
  | 0, _ => pure DArray.nil
  | i + 1, h => do
    let bs ← mmap_core i (le_of_ltₓ h)
    let b ← f (a.read ⟨i, h⟩)
    pure <| bs b

/-- Monadically map a function over the array. -/
@[inline]
def mmap {β : Type v} {m} [Monadₓ m] (a : Arrayₓ n α) (f : α → m β) : m (Arrayₓ n β) :=
  a.mmapCore f _ (le_reflₓ _)

/-- Map a function over the array. -/
@[inline]
def map {β : Type v} (a : Arrayₓ n α) (f : α → β) : Arrayₓ n β :=
  a.map fun _ => f

protected def Mem (v : α) (a : Arrayₓ n α) : Prop :=
  ∃ i : Finₓ n, read a i = v

instance : HasMem α (Arrayₓ n α) :=
  ⟨Arrayₓ.Mem⟩

theorem read_mem (a : Arrayₓ n α) i : read a i ∈ a :=
  Exists.introₓ i rfl

instance [HasRepr α] : HasRepr (Arrayₓ n α) :=
  ⟨reprₓ ∘ to_list⟩

unsafe instance [has_to_format α] : has_to_format (Arrayₓ n α) :=
  ⟨to_fmt ∘ to_list⟩

unsafe instance [has_to_tactic_format α] : has_to_tactic_format (Arrayₓ n α) :=
  ⟨tactic.pp ∘ to_list⟩

@[simp]
theorem read_write (a : Arrayₓ n α) (i : Finₓ n) (v : α) : read (write a i v) i = v :=
  DArray.read_write a i v

@[simp]
theorem read_write_of_ne (a : Arrayₓ n α) {i j : Finₓ n} (v : α) : i ≠ j → read (write a i v) j = read a j :=
  DArray.read_write_of_ne a v

def read' [Inhabited β] (a : Arrayₓ n β) (i : Nat) : β :=
  if h : i < n then a.read ⟨i, h⟩ else default

def write' (a : Arrayₓ n α) (i : Nat) (v : α) : Arrayₓ n α :=
  if h : i < n then a.write ⟨i, h⟩ v else a

theorem read_eq_read' [Inhabited α] (a : Arrayₓ n α) {i : Nat} (h : i < n) : read a ⟨i, h⟩ = read' a i := by
  simp [read', h]

theorem write_eq_write' (a : Arrayₓ n α) {i : Nat} (h : i < n) (v : α) : write a ⟨i, h⟩ v = write' a i v := by
  simp [write', h]

protected theorem ext {a b : Arrayₓ n α} (h : ∀ i, read a i = read b i) : a = b :=
  DArray.ext h

protected theorem ext' {a b : Arrayₓ n α} (h : ∀ i : Nat h : i < n, read a ⟨i, h⟩ = read b ⟨i, h⟩) : a = b :=
  DArray.ext' h

instance [DecidableEq α] : DecidableEq (Arrayₓ n α) := by
  unfold Arrayₓ
  infer_instance

end Arrayₓ

