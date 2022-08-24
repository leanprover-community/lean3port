/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

universe u w

def Buffer (α : Type u) :=
  Σn, Arrayₓ n α

def mkBuffer {α : Type u} : Buffer α :=
  ⟨0, { data := fun i => Finₓ.elim0 i }⟩

def Arrayₓ.toBuffer {α : Type u} {n : Nat} (a : Arrayₓ n α) : Buffer α :=
  ⟨n, a⟩

namespace Buffer

variable {α : Type u} {β : Type w}

def nil : Buffer α :=
  mkBuffer

def size (b : Buffer α) : Nat :=
  b.1

def toArray (b : Buffer α) : Arrayₓ b.size α :=
  b.2

def pushBack : Buffer α → α → Buffer α
  | ⟨n, a⟩, v => ⟨n + 1, a.pushBack v⟩

def popBack : Buffer α → Buffer α
  | ⟨0, a⟩ => ⟨0, a⟩
  | ⟨n + 1, a⟩ => ⟨n, a.popBack⟩

def read : ∀ b : Buffer α, Finₓ b.size → α
  | ⟨n, a⟩, i => a.read i

def write : ∀ b : Buffer α, Finₓ b.size → α → Buffer α
  | ⟨n, a⟩, i, v => ⟨n, a.write i v⟩

def read' [Inhabited α] : Buffer α → Nat → α
  | ⟨n, a⟩, i => a.read' i

def write' : Buffer α → Nat → α → Buffer α
  | ⟨n, a⟩, i, v => ⟨n, a.write' i v⟩

theorem read_eq_read' [Inhabited α] (b : Buffer α) (i : Nat) (h : i < b.size) : read b ⟨i, h⟩ = read' b i := by
  cases b <;> unfold read read' <;> simp [Arrayₓ.read_eq_read']

theorem write_eq_write' (b : Buffer α) (i : Nat) (h : i < b.size) (v : α) : write b ⟨i, h⟩ v = write' b i v := by
  cases b <;> unfold write write' <;> simp [Arrayₓ.write_eq_write']

def toList (b : Buffer α) : List α :=
  b.toArray.toList

protected def toString (b : Buffer Charₓ) : Stringₓ :=
  b.toArray.toList.asString

def appendList {α : Type u} : Buffer α → List α → Buffer α
  | b, [] => b
  | b, v :: vs => append_list (b.pushBack v) vs

def appendString (b : Buffer Charₓ) (s : Stringₓ) : Buffer Charₓ :=
  b.appendList s.toList

theorem lt_aux_1 {a b c : Nat} (h : a + c < b) : a < b :=
  lt_of_le_of_ltₓ (Nat.le_add_rightₓ a c) h

theorem lt_aux_2 {n : Nat} (h : 0 < n) : n - 1 < n :=
  Nat.sub_ltₓ h (Nat.succ_posₓ 0)

theorem lt_aux_3 {n i} (h : i + 1 < n) : n - 2 - i < n :=
  have : n > 0 := lt_transₓ (Nat.zero_lt_succₓ i) h
  have : n - 2 < n :=
    Nat.sub_ltₓ this
      (by
        decide)
  lt_of_le_of_ltₓ (Nat.sub_leₓ _ _) this

def appendArray {α : Type u} {n : Nat} (nz : 0 < n) : Buffer α → Arrayₓ n α → ∀ i : Nat, i < n → Buffer α
  | ⟨m, b⟩, a, 0, _ =>
    let i : Finₓ n := ⟨n - 1, lt_aux_2 nz⟩
    ⟨m + 1, b.pushBack (a.read i)⟩
  | ⟨m, b⟩, a, j + 1, h =>
    let i : Finₓ n := ⟨n - 2 - j, lt_aux_3 h⟩
    append_array ⟨m + 1, b.pushBack (a.read i)⟩ a j (lt_aux_1 h)

protected def append {α : Type u} : Buffer α → Buffer α → Buffer α
  | b, ⟨0, a⟩ => b
  | b, ⟨n + 1, a⟩ => appendArray (Nat.zero_lt_succₓ _) b a n (Nat.lt_succ_selfₓ _)

def iterate : ∀ b : Buffer α, β → (Finₓ b.size → α → β → β) → β
  | ⟨_, a⟩, b, f => a.iterate b f

def foreach : ∀ b : Buffer α, (Finₓ b.size → α → α) → Buffer α
  | ⟨n, a⟩, f => ⟨n, a.foreach f⟩

/-- Monadically map a function over the buffer. -/
@[inline]
def mmap {m} [Monadₓ m] (b : Buffer α) (f : α → m β) : m (Buffer β) := do
  let b' ← b.2.mmap f
  return b'

/-- Map a function over the buffer. -/
@[inline]
def map : Buffer α → (α → β) → Buffer β
  | ⟨n, a⟩, f => ⟨n, a.map f⟩

def foldl : Buffer α → β → (α → β → β) → β
  | ⟨_, a⟩, b, f => a.foldl b f

def revIterate : ∀ b : Buffer α, β → (Finₓ b.size → α → β → β) → β
  | ⟨_, a⟩, b, f => a.revIterate b f

def take (b : Buffer α) (n : Nat) : Buffer α :=
  if h : n ≤ b.size then ⟨n, b.toArray.take n h⟩ else b

def takeRight (b : Buffer α) (n : Nat) : Buffer α :=
  if h : n ≤ b.size then ⟨n, b.toArray.takeRight n h⟩ else b

def drop (b : Buffer α) (n : Nat) : Buffer α :=
  if h : n ≤ b.size then ⟨_, b.toArray.drop n h⟩ else b

def reverse (b : Buffer α) : Buffer α :=
  ⟨b.size, b.toArray.reverse⟩

protected def Mem (v : α) (a : Buffer α) : Prop :=
  ∃ i, read a i = v

instance : Membership α (Buffer α) :=
  ⟨Buffer.Mem⟩

instance : Append (Buffer α) :=
  ⟨Buffer.append⟩

instance [HasRepr α] : HasRepr (Buffer α) :=
  ⟨reprₓ ∘ to_list⟩

unsafe instance [has_to_format α] : has_to_format (Buffer α) :=
  ⟨to_fmt ∘ to_list⟩

unsafe instance [has_to_tactic_format α] : has_to_tactic_format (Buffer α) :=
  ⟨tactic.pp ∘ to_list⟩

end Buffer

def List.toBuffer {α : Type u} (l : List α) : Buffer α :=
  mkBuffer.appendList l

@[reducible]
def CharBuffer :=
  Buffer Charₓ

/-- Convert a format object into a character buffer with the provided
    formatting options. -/
unsafe axiom format.to_buffer : format → options → Buffer Charₓ

def Stringₓ.toCharBuffer (s : Stringₓ) : CharBuffer :=
  Buffer.nil.appendString s

