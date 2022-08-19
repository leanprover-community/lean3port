/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Leanbin.Init.Data.Array.Basic

def Array.ofFn (n : Nat) (f : Fin n → α) : Array α :=
  (mkArray n ()).mapIdx fun ⟨i, h⟩ () => f ⟨i, by simpa using h⟩

@[simp]
theorem Array.size_swap! (a : Array α) (i j) (hi : i < a.size) (hj : j < a.size) : (a.swap! i j).size = a.size := by
  simp [swap!, hi, hj]

theorem Array.size_reverse_rev (mid i) (a : Array α) (h : mid ≤ a.size) : (Array.reverse.rev a.size mid a i).size = a.size :=
  if hi : i < mid then by
    unfold Array.reverse.rev
    have : i < a.size := lt_of_lt_of_le hi h
    have : a.size - i - 1 < a.size := Nat.sub_lt_self i.zero_lt_succ this
    have := Array.size_reverse_rev mid (i+1) (a.swap! i (a.size - i - 1))
    simp_all
  else by
    unfold Array.reverse.rev
    simp [dif_neg hi]
termination_by _ => mid - i

@[simp]
theorem Array.size_reverse (a : Array α) : a.reverse.size = a.size := by
  have := size_reverse_rev (a.size / 2) 0 a (Nat.div_le_self ..)
  simp only [reverse, this]

universe u w

@[deprecated]
def Buffer (α : Type u) :=
  Array α

def mkBuffer {α : Type u} : Buffer α :=
  Array.empty

def Arrayₓ.toBuffer {α : Type u} {n : Nat} (a : Arrayₓ n α) : Buffer α :=
  Array.ofFn n a.1

namespace Buffer

variable {α : Type u} {β : Type w}

def nil : Buffer α :=
  mkBuffer

abbrev size (b : Buffer α) : Nat :=
  Array.size b

instance : GetElem (Buffer α) Nat α fun b i => i < b.size :=
  inferInstanceAs (GetElem (Array α) _ _ _)

def toArray (b : Buffer α) : Arrayₓ b.size α :=
  ⟨b.get⟩

def pushBack : Buffer α → α → Buffer α
  | a, v => a.push v

def popBack : Buffer α → Buffer α
  | a => a.pop

def read : ∀ b : Buffer α, Fin b.size → α
  | a, i => a[i]

def write : ∀ b : Buffer α, Fin b.size → α → Buffer α
  | a, i, v => a.set i v

def read' [Inhabited α] : Buffer α → Nat → α
  | a, i => a[i]!

def write' : Buffer α → Nat → α → Buffer α
  | a, i, v => a.set! i v

theorem read_eq_read' [Inhabited α] (b : Buffer α) (i : Nat) (h : i < b.size) : read b ⟨i, h⟩ = read' b i := by
  simp [read, read', getElem!, h]

theorem write_eq_write' (b : Buffer α) (i : Nat) (h : i < b.size) (v : α) : write b ⟨i, h⟩ v = write' b i v := by
  simp [write, write', Array.set!, Array.setD, h]

def toList (b : Buffer α) : List α :=
  Array.toList b

protected def toString (b : Buffer Char) : String :=
  b.toList.asString

def appendList {α : Type u} : Buffer α → List α → Buffer α
  | b, vs => Array.appendList b vs

def appendString (b : Buffer Char) (s : String) : Buffer Char :=
  b.appendList s.toList

theorem lt_aux_1 {a b c : Nat} (h : a + c < b) : a < b :=
  lt_of_le_of_lt (Nat.le_add_right a c) h

theorem lt_aux_2 {n : Nat} (h : 0 < n) : n - 1 < n :=
  Nat.sub_lt h (Nat.succ_pos 0)

theorem lt_aux_3 {n i} (h : i + 1 < n) : n - 2 - i < n :=
  have : n > 0 := lt_trans (Nat.zero_lt_succ i) h
  have : n - 2 < n :=
    Nat.sub_lt this
      (by
        decide)
  lt_of_le_of_lt (Nat.sub_le _ _) this

def appendArray {α : Type u} {n : Nat} (nz : 0 < n) : Buffer α → Arrayₓ n α → ∀ i : Nat, i < n → Buffer α
  | b, a, 0, _ =>
    let i : Fin n := ⟨n - 1, lt_aux_2 nz⟩
    b.pushBack (a.read i)
  | b, a, j + 1, h =>
    let i : Fin n := ⟨n - 2 - j, lt_aux_3 h⟩
    appendArray nz (b.pushBack (a.read i)) a j (lt_aux_1 h)

protected def append {α : Type u} : Buffer α → Buffer α → Buffer α
  | b, a => Array.append b a

def iterate : ∀ b : Buffer α, β → (Fin b.size → α → β → β) → β
  | a, b, f => Id.run do
    let mut b := b
    for h : i in [0:a.size] do
      have : i < a.size := h.2
      b := f ⟨i, this⟩ a[i] b
    return b

def foreach : ∀ b : Buffer α, (Fin b.size → α → α) → Buffer α
  | a, f => a.mapIdx f

/-- Monadically map a function over the buffer. -/
@[inline]
def mmap {m} [Monad m] (b : Buffer α) (f : α → m β) : m (Buffer β) :=
  Array.mapM f b

/-- Map a function over the buffer. -/
@[inline]
def map : Buffer α → (α → β) → Buffer β
  | a, f => Array.map f a

def foldl : Buffer α → β → (α → β → β) → β
  | a, b, f => Array.foldl (Function.swap f) b a

def revIterate : ∀ b : Buffer α, β → (Fin b.size → α → β → β) → β
  | a, b, f => Buffer.iterate a.reverse b (by simpa [size] using f)

def take (b : Buffer α) (n : Nat) : Buffer α :=
  b[:n].toArray

def takeRight (b : Buffer α) (n : Nat) : Buffer α :=
  b[b.size - n :].toArray

def drop (b : Buffer α) (n : Nat) : Buffer α :=
  b[n:].toArray

def reverse (b : Buffer α) : Buffer α :=
  Array.reverse b

protected def Mem (v : α) (a : Buffer α) : Prop :=
  ∃ i, read a i = v

instance : Membership α (Buffer α) :=
  ⟨Buffer.Mem⟩

instance : Append (Buffer α) :=
  ⟨Buffer.append⟩

end Buffer

def List.toBuffer {α : Type u} (l : List α) : Buffer α :=
  mkBuffer.appendList l

@[reducible]
def CharBuffer :=
  Buffer Char

def String.toCharBuffer (s : String) : CharBuffer :=
  Buffer.nil.appendString s

