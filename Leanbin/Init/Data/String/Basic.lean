/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.List.Basic
import Leanbin.Init.Data.Char.Basic

/- In the VM, strings are implemented using a dynamic array and UTF-8 encoding.

   TODO: we currently cannot mark string_imp as private because
   we need to bind string_imp.mk and string_imp.cases_on in the VM.
-/
/- In the VM, strings are implemented using a dynamic array and UTF-8 encoding.

   TODO: we currently cannot mark string_imp as private because
   we need to bind string_imp.mk and string_imp.cases_on in the VM.
-/
structure StringImp where
  data : List Charₓ

def Stringₓ :=
  StringImp

def List.asStringₓ (s : List Charₓ) : Stringₓ :=
  ⟨s⟩

namespace Stringₓ

instance : LT Stringₓ :=
  ⟨fun s₁ s₂ => s₁.data < s₂.data⟩

-- Remark: this function has a VM builtin efficient implementation.
instance hasDecidableLt (s₁ s₂ : Stringₓ) : Decidable (s₁ < s₂) :=
  List.hasDecidableLtₓ s₁.data s₂.data

instance hasDecidableEq : DecidableEq Stringₓ := fun ⟨x⟩ ⟨y⟩ =>
  match List.hasDecEqₓ x y with
  | is_true p => isTrue (congr_arg StringImp.mk p)
  | is_false p => isFalse fun q => p (StringImp.mk.inj q)

def empty : Stringₓ :=
  ⟨[]⟩

def length : Stringₓ → Nat
  | ⟨s⟩ => s.length

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/
def push : Stringₓ → Charₓ → Stringₓ
  | ⟨s⟩, c => ⟨s ++ [c]⟩

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/
def append : Stringₓ → Stringₓ → Stringₓ
  | ⟨a⟩, ⟨b⟩ => ⟨a ++ b⟩

-- O(n) in the VM, where n is the length of the string
def toList : Stringₓ → List Charₓ
  | ⟨s⟩ => s

def fold {α} (a : α) (f : α → Charₓ → α) (s : Stringₓ) : α :=
  s.toList.foldl f a

/- In the VM, the string iterator is implemented as a pointer to the string being iterated + index.

   TODO: we currently cannot mark interator_imp as private because
   we need to bind string_imp.mk and string_imp.cases_on in the VM.
-/
structure IteratorImp where
  fst : List Charₓ
  snd : List Charₓ

def Iterator :=
  iterator_imp

def mkIterator : Stringₓ → Iterator
  | ⟨s⟩ => ⟨[], s⟩

namespace Iterator

def curr : Iterator → Charₓ
  | ⟨p, c :: n⟩ => c
  | _ => default

/- In the VM, `set_curr` is constant time if the string being iterated is not shared and linear time
   if it is. -/
def setCurr : Iterator → Charₓ → Iterator
  | ⟨p, c :: n⟩, c' => ⟨p, c' :: n⟩
  | it, c' => it

def next : Iterator → Iterator
  | ⟨p, c :: n⟩ => ⟨c :: p, n⟩
  | ⟨p, []⟩ => ⟨p, []⟩

def prev : Iterator → Iterator
  | ⟨c :: p, n⟩ => ⟨p, c :: n⟩
  | ⟨[], n⟩ => ⟨[], n⟩

def hasNext : Iterator → Bool
  | ⟨p, []⟩ => false
  | _ => true

def hasPrev : Iterator → Bool
  | ⟨[], n⟩ => false
  | _ => true

def insert : Iterator → Stringₓ → Iterator
  | ⟨p, n⟩, ⟨s⟩ => ⟨p, s ++ n⟩

def remove : Iterator → Nat → Iterator
  | ⟨p, n⟩, m => ⟨p, n.drop m⟩

-- In the VM, `to_string` is a constant time operation.
def toString : Iterator → Stringₓ
  | ⟨p, n⟩ => ⟨p.reverse ++ n⟩

def toEnd : Iterator → Iterator
  | ⟨p, n⟩ => ⟨n.reverse ++ p, []⟩

def nextToString : Iterator → Stringₓ
  | ⟨p, n⟩ => ⟨n⟩

def prevToString : Iterator → Stringₓ
  | ⟨p, n⟩ => ⟨p.reverse⟩

protected def extractCore : List Charₓ → List Charₓ → Option (List Charₓ)
  | [], cs => none
  | c :: cs₁, cs₂ =>
    if cs₁ = cs₂ then some [c]
    else
      match extract_core cs₁ cs₂ with
      | none => none
      | some r => some (c :: r)

def extract : Iterator → Iterator → Option Stringₓ
  | ⟨p₁, n₁⟩, ⟨p₂, n₂⟩ =>
    if p₁.reverse ++ n₁ ≠ p₂.reverse ++ n₂ then none
    else
      if n₁ = n₂ then some ""
      else
        match Iterator.extractCore n₁ n₂ with
        | none => none
        | some r => some ⟨r⟩

end Iterator

end Stringₓ

-- The following definitions do not have builtin support in the VM
instance : Inhabited Stringₓ :=
  ⟨Stringₓ.empty⟩

instance : SizeOf Stringₓ :=
  ⟨Stringₓ.length⟩

instance : Append Stringₓ :=
  ⟨Stringₓ.append⟩

namespace Stringₓ

def str : Stringₓ → Charₓ → Stringₓ :=
  push

def isEmpty (s : Stringₓ) : Bool :=
  toBool (s.length = 0)

def front (s : Stringₓ) : Charₓ :=
  s.mkIterator.curr

def back (s : Stringₓ) : Charₓ :=
  s.mkIterator.toEnd.prev.curr

def join (l : List Stringₓ) : Stringₓ :=
  l.foldl (fun r s => r ++ s) ""

def singleton (c : Charₓ) : Stringₓ :=
  empty.push c

def intercalate (s : Stringₓ) (ss : List Stringₓ) : Stringₓ :=
  (List.intercalate s.toList (ss.map toList)).asString

namespace Iterator

def nextn : Iterator → Nat → Iterator
  | it, 0 => it
  | it, i + 1 => nextn it.next i

def prevn : Iterator → Nat → Iterator
  | it, 0 => it
  | it, i + 1 => prevn it.prev i

end Iterator

def popBack (s : Stringₓ) : Stringₓ :=
  s.mkIterator.toEnd.prev.prevToString

def popnBack (s : Stringₓ) (n : Nat) : Stringₓ :=
  (s.mkIterator.toEnd.prevn n).prevToString

def backn (s : Stringₓ) (n : Nat) : Stringₓ :=
  (s.mkIterator.toEnd.prevn n).nextToString

end Stringₓ

protected def Charₓ.toString (c : Charₓ) : Stringₓ :=
  Stringₓ.singleton c

private def to_nat_core : Stringₓ.Iterator → Nat → Nat → Nat
  | it, 0, r => r
  | it, i + 1, r =>
    let c := it.curr
    let r := r * 10 + c.toNat - '0'.toNat
    to_nat_core it.next i r

def Stringₓ.toNat (s : Stringₓ) : Nat :=
  toNatCore s.mkIterator s.length 0

namespace Stringₓ

private theorem nil_ne_append_singleton : ∀ (c : Charₓ) (l : List Charₓ), [] ≠ l ++ [c]
  | c, [] => fun h => List.noConfusion h
  | c, d :: l => fun h => List.noConfusion h

theorem empty_ne_str : ∀ (c : Charₓ) (s : Stringₓ), Empty ≠ str s c
  | c, ⟨l⟩ => fun h : StringImp.mk [] = StringImp.mk (l ++ [c]) =>
    (StringImp.noConfusion h) fun h => nil_ne_append_singleton _ _ h

theorem str_ne_empty (c : Charₓ) (s : Stringₓ) : str s c ≠ Empty :=
  (empty_ne_str c s).symm

private theorem str_ne_str_left_aux : ∀ {c₁ c₂ : Charₓ} (l₁ l₂ : List Charₓ), c₁ ≠ c₂ → l₁ ++ [c₁] ≠ l₂ ++ [c₂]
  | c₁, c₂, [], [], h₁, h₂ => List.noConfusion h₂ fun h _ => absurd h h₁
  | c₁, c₂, d₁ :: l₁, [], h₁, h₂ =>
    have : d₁ :: (l₁ ++ [c₁]) = [c₂] := h₂
    have : l₁ ++ [c₁] = [] := List.noConfusion this fun _ h => h
    absurd this.symm (nil_ne_append_singleton _ _)
  | c₁, c₂, [], d₂ :: l₂, h₁, h₂ =>
    have : [c₁] = d₂ :: (l₂ ++ [c₂]) := h₂
    have : [] = l₂ ++ [c₂] := List.noConfusion this fun _ h => h
    absurd this (nil_ne_append_singleton _ _)
  | c₁, c₂, d₁ :: l₁, d₂ :: l₂, h₁, h₂ =>
    have : d₁ :: (l₁ ++ [c₁]) = d₂ :: (l₂ ++ [c₂]) := h₂
    have : l₁ ++ [c₁] = l₂ ++ [c₂] := List.noConfusion this fun _ h => h
    absurd this (str_ne_str_left_aux l₁ l₂ h₁)

theorem str_ne_str_left : ∀ {c₁ c₂ : Charₓ} (s₁ s₂ : Stringₓ), c₁ ≠ c₂ → str s₁ c₁ ≠ str s₂ c₂
  | c₁, c₂, StringImp.mk l₁, StringImp.mk l₂, h₁, h₂ =>
    have : l₁ ++ [c₁] = l₂ ++ [c₂] := StringImp.noConfusion h₂ id
    absurd this (str_ne_str_left_aux l₁ l₂ h₁)

private theorem str_ne_str_right_aux : ∀ (c₁ c₂ : Charₓ) {l₁ l₂ : List Charₓ}, l₁ ≠ l₂ → l₁ ++ [c₁] ≠ l₂ ++ [c₂]
  | c₁, c₂, [], [], h₁, h₂ => absurd rfl h₁
  | c₁, c₂, d₁ :: l₁, [], h₁, h₂ =>
    have : d₁ :: (l₁ ++ [c₁]) = [c₂] := h₂
    have : l₁ ++ [c₁] = [] := List.noConfusion this fun _ h => h
    absurd this.symm (nil_ne_append_singleton _ _)
  | c₁, c₂, [], d₂ :: l₂, h₁, h₂ =>
    have : [c₁] = d₂ :: (l₂ ++ [c₂]) := h₂
    have : [] = l₂ ++ [c₂] := List.noConfusion this fun _ h => h
    absurd this (nil_ne_append_singleton _ _)
  | c₁, c₂, d₁ :: l₁, d₂ :: l₂, h₁, h₂ =>
    have aux₁ : d₁ :: (l₁ ++ [c₁]) = d₂ :: (l₂ ++ [c₂]) := h₂
    have : d₁ = d₂ := List.noConfusion aux₁ fun h _ => h
    have aux₂ : l₁ ≠ l₂ := fun h =>
      have : d₁ :: l₁ = d₂ :: l₂ := Eq.subst h (Eq.subst this rfl)
      absurd this h₁
    have : l₁ ++ [c₁] = l₂ ++ [c₂] := List.noConfusion aux₁ fun _ h => h
    absurd this (str_ne_str_right_aux c₁ c₂ aux₂)

theorem str_ne_str_right : ∀ (c₁ c₂ : Charₓ) {s₁ s₂ : Stringₓ}, s₁ ≠ s₂ → str s₁ c₁ ≠ str s₂ c₂
  | c₁, c₂, StringImp.mk l₁, StringImp.mk l₂, h₁, h₂ =>
    have aux : l₁ ≠ l₂ := fun h =>
      have : StringImp.mk l₁ = StringImp.mk l₂ := Eq.subst h rfl
      absurd this h₁
    have : l₁ ++ [c₁] = l₂ ++ [c₂] := StringImp.noConfusion h₂ id
    absurd this (str_ne_str_right_aux c₁ c₂ aux)

end Stringₓ

