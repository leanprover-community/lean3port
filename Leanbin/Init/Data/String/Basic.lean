/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.string.basic
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.List.Basic
import Leanbin.Init.Data.Char.Basic

/-- In the VM, strings are implemented using a dynamic array and UTF-8 encoding.

   TODO: we currently cannot mark string_imp as private because
   we need to bind string_imp.mk and string_imp.cases_on in the VM.
-/
structure StringImp where
  data : List Char
#align string_imp StringImp

#print String /-
def String :=
  StringImp
#align string String
-/

#print List.asString /-
def List.asString (s : List Char) : String :=
  ⟨s⟩
#align list.as_string List.asString
-/

namespace String

instance : LT String :=
  ⟨fun s₁ s₂ => s₁.data < s₂.data⟩

/-- Remark: this function has a VM builtin efficient implementation. -/
instance hasDecidableLt (s₁ s₂ : String) : Decidable (s₁ < s₂) :=
  List.hasDecidableLt s₁.data s₂.data
#align string.has_decidable_lt String.hasDecidableLt

instance hasDecidableEq : DecidableEq String := fun ⟨x⟩ ⟨y⟩ =>
  match List.hasDecEq x y with
  | is_true p => isTrue (congr_arg StringImp.mk p)
  | is_false p => isFalse fun q => p (StringImp.mk.inj q)
#align string.has_decidable_eq String.hasDecidableEq

def empty : String :=
  ⟨[]⟩
#align string.empty String.empty

#print String.length /-
def length : String → Nat
  | ⟨s⟩ => s.length
#align string.length String.length
-/

#print String.push /-
/-- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/
def push : String → Char → String
  | ⟨s⟩, c => ⟨s ++ [c]⟩
#align string.push String.push
-/

#print String.append /-
/-- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/
def append : String → String → String
  | ⟨a⟩, ⟨b⟩ => ⟨a ++ b⟩
#align string.append String.append
-/

#print String.toList /-
/-- O(n) in the VM, where n is the length of the string -/
def toList : String → List Char
  | ⟨s⟩ => s
#align string.to_list String.toList
-/

def fold {α} (a : α) (f : α → Char → α) (s : String) : α :=
  s.toList.foldl f a
#align string.fold String.fold

/-- In the VM, the string iterator is implemented as a pointer to the string being iterated + index.

   TODO: we currently cannot mark interator_imp as private because
   we need to bind string_imp.mk and string_imp.cases_on in the VM.
-/
structure IteratorImp where
  fst : List Char
  snd : List Char
#align string.iterator_imp String.IteratorImp

#print String.Iterator /-
def Iterator :=
  iterator_imp
#align string.iterator String.Iterator
-/

#print String.mkIterator /-
def mkIterator : String → Iterator
  | ⟨s⟩ => ⟨[], s⟩
#align string.mk_iterator String.mkIterator
-/

namespace Iterator

#print String.Iterator.curr /-
def curr : Iterator → Char
  | ⟨p, c :: n⟩ => c
  | _ => default
#align string.iterator.curr String.Iterator.curr
-/

#print String.Iterator.setCurr /-
/--
In the VM, `set_curr` is constant time if the string being iterated is not shared and linear time
   if it is. -/
def setCurr : Iterator → Char → Iterator
  | ⟨p, c :: n⟩, c' => ⟨p, c' :: n⟩
  | it, c' => it
#align string.iterator.set_curr String.Iterator.setCurr
-/

#print String.Iterator.next /-
def next : Iterator → Iterator
  | ⟨p, c :: n⟩ => ⟨c :: p, n⟩
  | ⟨p, []⟩ => ⟨p, []⟩
#align string.iterator.next String.Iterator.next
-/

#print String.Iterator.prev /-
def prev : Iterator → Iterator
  | ⟨c :: p, n⟩ => ⟨p, c :: n⟩
  | ⟨[], n⟩ => ⟨[], n⟩
#align string.iterator.prev String.Iterator.prev
-/

#print String.Iterator.hasNext /-
def hasNext : Iterator → Bool
  | ⟨p, []⟩ => false
  | _ => true
#align string.iterator.has_next String.Iterator.hasNext
-/

#print String.Iterator.hasPrev /-
def hasPrev : Iterator → Bool
  | ⟨[], n⟩ => false
  | _ => true
#align string.iterator.has_prev String.Iterator.hasPrev
-/

def insert : Iterator → String → Iterator
  | ⟨p, n⟩, ⟨s⟩ => ⟨p, s ++ n⟩
#align string.iterator.insert String.Iterator.insert

def remove : Iterator → Nat → Iterator
  | ⟨p, n⟩, m => ⟨p, n.drop m⟩
#align string.iterator.remove String.Iterator.remove

#print String.Iterator.toString /-
/-- In the VM, `to_string` is a constant time operation. -/
def toString : Iterator → String
  | ⟨p, n⟩ => ⟨p.reverse ++ n⟩
#align string.iterator.to_string String.Iterator.toString
-/

#print String.Iterator.toEnd /-
def toEnd : Iterator → Iterator
  | ⟨p, n⟩ => ⟨n.reverse ++ p, []⟩
#align string.iterator.to_end String.Iterator.toEnd
-/

def nextToString : Iterator → String
  | ⟨p, n⟩ => ⟨n⟩
#align string.iterator.next_to_string String.Iterator.nextToString

def prevToString : Iterator → String
  | ⟨p, n⟩ => ⟨p.reverse⟩
#align string.iterator.prev_to_string String.Iterator.prevToString

protected def extractCore : List Char → List Char → Option (List Char)
  | [], cs => none
  | c :: cs₁, cs₂ =>
    if cs₁ = cs₂ then some [c]
    else
      match extract_core cs₁ cs₂ with
      | none => none
      | some r => some (c :: r)
#align string.iterator.extract_core String.Iterator.extractCore

/- warning: string.iterator.extract -> String.Iterator.extract is a dubious translation:
lean 3 declaration is
  String.Iterator -> String.Iterator -> (Option.{0} String)
but is expected to have type
  String.Iterator -> String.Iterator -> String
Case conversion may be inaccurate. Consider using '#align string.iterator.extract String.Iterator.extractₓ'. -/
def extract : Iterator → Iterator → Option String
  | ⟨p₁, n₁⟩, ⟨p₂, n₂⟩ =>
    if p₁.reverse ++ n₁ ≠ p₂.reverse ++ n₂ then none
    else
      if n₁ = n₂ then some ""
      else
        match Iterator.extractCore n₁ n₂ with
        | none => none
        | some r => some ⟨r⟩
#align string.iterator.extract String.Iterator.extract

end Iterator

end String

/-! The following definitions do not have builtin support in the VM -/


instance : Inhabited String :=
  ⟨String.empty⟩

instance : SizeOf String :=
  ⟨String.length⟩

instance : Append String :=
  ⟨String.append⟩

namespace String

#print String.str /-
def str : String → Char → String :=
  Push
#align string.str String.str
-/

#print String.isEmpty /-
def isEmpty (s : String) : Bool :=
  decide (s.length = 0)
#align string.is_empty String.isEmpty
-/

#print String.front /-
def front (s : String) : Char :=
  s.mkIterator.curr
#align string.front String.front
-/

#print String.back /-
def back (s : String) : Char :=
  s.mkIterator.toEnd.prev.curr
#align string.back String.back
-/

#print String.join /-
def join (l : List String) : String :=
  l.foldl (fun r s => r ++ s) ""
#align string.join String.join
-/

#print String.singleton /-
def singleton (c : Char) : String :=
  empty.push c
#align string.singleton String.singleton
-/

#print String.intercalate /-
def intercalate (s : String) (ss : List String) : String :=
  (List.intercalate s.toList (ss.map toList)).asString
#align string.intercalate String.intercalate
-/

namespace Iterator

#print String.Iterator.nextn /-
def nextn : Iterator → Nat → Iterator
  | it, 0 => it
  | it, i + 1 => nextn it.next i
#align string.iterator.nextn String.Iterator.nextn
-/

#print String.Iterator.prevn /-
def prevn : Iterator → Nat → Iterator
  | it, 0 => it
  | it, i + 1 => prevn it.prev i
#align string.iterator.prevn String.Iterator.prevn
-/

end Iterator

def popBack (s : String) : String :=
  s.mkIterator.toEnd.prev.prevToString
#align string.pop_back String.popBack

def popnBack (s : String) (n : Nat) : String :=
  (s.mkIterator.toEnd.prevn n).prevToString
#align string.popn_back String.popnBack

def backn (s : String) (n : Nat) : String :=
  (s.mkIterator.toEnd.prevn n).nextToString
#align string.backn String.backn

end String

#print Char.toString /-
protected def Char.toString (c : Char) : String :=
  String.singleton c
#align char.to_string Char.toString
-/

private def to_nat_core : String.Iterator → Nat → Nat → Nat
  | it, 0, r => r
  | it, i + 1, r =>
    let c := it.curr
    let r := r * 10 + c.toNat - '0'.toNat
    to_nat_core it.next i r
#align to_nat_core to_nat_core

def String.toNat (s : String) : Nat :=
  toNatCore s.mkIterator s.length 0
#align string.to_nat String.toNat

namespace String

private theorem nil_ne_append_singleton : ∀ (c : Char) (l : List Char), [] ≠ l ++ [c]
  | c, [] => fun h => List.noConfusion h
  | c, d :: l => fun h => List.noConfusion h
#align string.nil_ne_append_singleton string.nil_ne_append_singleton

theorem empty_ne_str : ∀ (c : Char) (s : String), Empty ≠ str s c
  | c, ⟨l⟩ => fun h : StringImp.mk [] = StringImp.mk (l ++ [c]) =>
    (StringImp.noConfusion h) fun h => nil_ne_append_singleton _ _ h
#align string.empty_ne_str String.empty_ne_str

theorem str_ne_empty (c : Char) (s : String) : str s c ≠ Empty :=
  (empty_ne_str c s).symm
#align string.str_ne_empty String.str_ne_empty

private theorem str_ne_str_left_aux :
    ∀ {c₁ c₂ : Char} (l₁ l₂ : List Char), c₁ ≠ c₂ → l₁ ++ [c₁] ≠ l₂ ++ [c₂]
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
#align string.str_ne_str_left_aux string.str_ne_str_left_aux

theorem str_ne_str_left : ∀ {c₁ c₂ : Char} (s₁ s₂ : String), c₁ ≠ c₂ → str s₁ c₁ ≠ str s₂ c₂
  | c₁, c₂, StringImp.mk l₁, StringImp.mk l₂, h₁, h₂ =>
    have : l₁ ++ [c₁] = l₂ ++ [c₂] := StringImp.noConfusion h₂ id
    absurd this (str_ne_str_left_aux l₁ l₂ h₁)
#align string.str_ne_str_left String.str_ne_str_left

private theorem str_ne_str_right_aux :
    ∀ (c₁ c₂ : Char) {l₁ l₂ : List Char}, l₁ ≠ l₂ → l₁ ++ [c₁] ≠ l₂ ++ [c₂]
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
#align string.str_ne_str_right_aux string.str_ne_str_right_aux

theorem str_ne_str_right : ∀ (c₁ c₂ : Char) {s₁ s₂ : String}, s₁ ≠ s₂ → str s₁ c₁ ≠ str s₂ c₂
  | c₁, c₂, StringImp.mk l₁, StringImp.mk l₂, h₁, h₂ =>
    have aux : l₁ ≠ l₂ := fun h =>
      have : StringImp.mk l₁ = StringImp.mk l₂ := Eq.subst h rfl
      absurd this h₁
    have : l₁ ++ [c₁] = l₂ ++ [c₂] := StringImp.noConfusion h₂ id
    absurd this (str_ne_str_right_aux c₁ c₂ aux)
#align string.str_ne_str_right String.str_ne_str_right

end String

