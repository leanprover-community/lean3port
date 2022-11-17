/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

universe u w

def Buffer (α : Type u) :=
  Σ n, Array' n α
#align buffer Buffer

def mkBuffer {α : Type u} : Buffer α :=
  ⟨0, { data := fun i => Fin.elim0 i }⟩
#align mk_buffer mkBuffer

def Array'.toBuffer {α : Type u} {n : Nat} (a : Array' n α) : Buffer α :=
  ⟨n, a⟩
#align array.to_buffer Array'.toBuffer

namespace Buffer

variable {α : Type u} {β : Type w}

def nil : Buffer α :=
  mkBuffer
#align buffer.nil Buffer.nil

def size (b : Buffer α) : Nat :=
  b.1
#align buffer.size Buffer.size

def toArray (b : Buffer α) : Array' b.size α :=
  b.2
#align buffer.to_array Buffer.toArray

def pushBack : Buffer α → α → Buffer α
  | ⟨n, a⟩, v => ⟨n + 1, a.pushBack v⟩
#align buffer.push_back Buffer.pushBack

def popBack : Buffer α → Buffer α
  | ⟨0, a⟩ => ⟨0, a⟩
  | ⟨n + 1, a⟩ => ⟨n, a.popBack⟩
#align buffer.pop_back Buffer.popBack

def read : ∀ b : Buffer α, Fin b.size → α
  | ⟨n, a⟩, i => a.read i
#align buffer.read Buffer.read

def write : ∀ b : Buffer α, Fin b.size → α → Buffer α
  | ⟨n, a⟩, i, v => ⟨n, a.write i v⟩
#align buffer.write Buffer.write

def read' [Inhabited α] : Buffer α → Nat → α
  | ⟨n, a⟩, i => a.read' i
#align buffer.read' Buffer.read'

def write' : Buffer α → Nat → α → Buffer α
  | ⟨n, a⟩, i, v => ⟨n, a.write' i v⟩
#align buffer.write' Buffer.write'

theorem read_eq_read' [Inhabited α] (b : Buffer α) (i : Nat) (h : i < b.size) : read b ⟨i, h⟩ = read' b i := by
  cases b <;> unfold read read' <;> simp [Array'.read_eq_read']
#align buffer.read_eq_read' Buffer.read_eq_read'

theorem write_eq_write' (b : Buffer α) (i : Nat) (h : i < b.size) (v : α) : write b ⟨i, h⟩ v = write' b i v := by
  cases b <;> unfold write write' <;> simp [Array'.write_eq_write']
#align buffer.write_eq_write' Buffer.write_eq_write'

def toList (b : Buffer α) : List α :=
  b.toArray.toList
#align buffer.to_list Buffer.toList

protected def toString (b : Buffer Char) : String :=
  b.toArray.toList.asString
#align buffer.to_string Buffer.toString

def appendList {α : Type u} : Buffer α → List α → Buffer α
  | b, [] => b
  | b, v :: vs => append_list (b.pushBack v) vs
#align buffer.append_list Buffer.appendList

def appendString (b : Buffer Char) (s : String) : Buffer Char :=
  b.appendList s.toList
#align buffer.append_string Buffer.appendString

theorem lt_aux_1 {a b c : Nat} (h : a + c < b) : a < b :=
  lt_of_le_of_lt (Nat.le_add_right a c) h
#align buffer.lt_aux_1 Buffer.lt_aux_1

theorem lt_aux_2 {n : Nat} (h : 0 < n) : n - 1 < n :=
  Nat.sub_lt h (Nat.succ_pos 0)
#align buffer.lt_aux_2 Buffer.lt_aux_2

theorem lt_aux_3 {n i} (h : i + 1 < n) : n - 2 - i < n :=
  have : n > 0 := lt_trans (Nat.zero_lt_succ i) h
  have : n - 2 < n := Nat.sub_lt this dec_trivial
  lt_of_le_of_lt (Nat.sub_le _ _) this
#align buffer.lt_aux_3 Buffer.lt_aux_3

def appendArray {α : Type u} {n : Nat} (nz : 0 < n) : Buffer α → Array' n α → ∀ i : Nat, i < n → Buffer α
  | ⟨m, b⟩, a, 0, _ =>
    let i : Fin n := ⟨n - 1, lt_aux_2 nz⟩
    ⟨m + 1, b.pushBack (a.read i)⟩
  | ⟨m, b⟩, a, j + 1, h =>
    let i : Fin n := ⟨n - 2 - j, lt_aux_3 h⟩
    append_array ⟨m + 1, b.pushBack (a.read i)⟩ a j (lt_aux_1 h)
#align buffer.append_array Buffer.appendArray

protected def append {α : Type u} : Buffer α → Buffer α → Buffer α
  | b, ⟨0, a⟩ => b
  | b, ⟨n + 1, a⟩ => appendArray (Nat.zero_lt_succ _) b a n (Nat.lt_succ_self _)
#align buffer.append Buffer.append

def iterate : ∀ b : Buffer α, β → (Fin b.size → α → β → β) → β
  | ⟨_, a⟩, b, f => a.iterate b f
#align buffer.iterate Buffer.iterate

def foreach : ∀ b : Buffer α, (Fin b.size → α → α) → Buffer α
  | ⟨n, a⟩, f => ⟨n, a.foreach f⟩
#align buffer.foreach Buffer.foreach

/-- Monadically map a function over the buffer. -/
@[inline]
def mmap {m} [Monad m] (b : Buffer α) (f : α → m β) : m (Buffer β) := do
  let b' ← b.2.mmap f
  return b'
#align buffer.mmap Buffer.mmap

/-- Map a function over the buffer. -/
@[inline]
def map : Buffer α → (α → β) → Buffer β
  | ⟨n, a⟩, f => ⟨n, a.map f⟩
#align buffer.map Buffer.map

def foldl : Buffer α → β → (α → β → β) → β
  | ⟨_, a⟩, b, f => a.foldl b f
#align buffer.foldl Buffer.foldl

def revIterate : ∀ b : Buffer α, β → (Fin b.size → α → β → β) → β
  | ⟨_, a⟩, b, f => a.revIterate b f
#align buffer.rev_iterate Buffer.revIterate

def take (b : Buffer α) (n : Nat) : Buffer α :=
  if h : n ≤ b.size then ⟨n, b.toArray.take n h⟩ else b
#align buffer.take Buffer.take

def takeRight (b : Buffer α) (n : Nat) : Buffer α :=
  if h : n ≤ b.size then ⟨n, b.toArray.takeRight n h⟩ else b
#align buffer.take_right Buffer.takeRight

def drop (b : Buffer α) (n : Nat) : Buffer α :=
  if h : n ≤ b.size then ⟨_, b.toArray.drop n h⟩ else b
#align buffer.drop Buffer.drop

def reverse (b : Buffer α) : Buffer α :=
  ⟨b.size, b.toArray.reverse⟩
#align buffer.reverse Buffer.reverse

protected def Mem (v : α) (a : Buffer α) : Prop :=
  ∃ i, read a i = v
#align buffer.mem Buffer.Mem

instance : Membership α (Buffer α) :=
  ⟨Buffer.Mem⟩

instance : Append (Buffer α) :=
  ⟨Buffer.append⟩

instance [Repr α] : Repr (Buffer α) :=
  ⟨repr ∘ to_list⟩

unsafe instance [has_to_format α] : has_to_format (Buffer α) :=
  ⟨to_fmt ∘ to_list⟩

unsafe instance [has_to_tactic_format α] : has_to_tactic_format (Buffer α) :=
  ⟨tactic.pp ∘ to_list⟩

end Buffer

def List.toBuffer {α : Type u} (l : List α) : Buffer α :=
  mkBuffer.appendList l
#align list.to_buffer List.toBuffer

@[reducible]
def CharBuffer :=
  Buffer Char
#align char_buffer CharBuffer

/-- Convert a format object into a character buffer with the provided
    formatting options. -/
unsafe axiom format.to_buffer : format → options → Buffer Char
#align format.to_buffer format.to_buffer

def String.toCharBuffer (s : String) : CharBuffer :=
  Buffer.nil.appendString s
#align string.to_char_buffer String.toCharBuffer

