prelude
import Leanbin.Init.Data.List.Basic
import Leanbin.Init.Data.Char.Basic

structure StringImp where
  data : List Charₓ

def Stringₓ :=
  StringImp

def List.asStringₓ (s : List Charₓ) : Stringₓ :=
  ⟨s⟩

namespace Stringₓ

instance : LT Stringₓ :=
  ⟨fun s₁ s₂ => s₁.data < s₂.data⟩

instance has_decidable_lt (s₁ s₂ : Stringₓ) : Decidable (s₁ < s₂) :=
  List.hasDecidableLtₓ s₁.data s₂.data

instance has_decidable_eq : DecidableEq Stringₓ := fun ⟨x⟩ ⟨y⟩ =>
  match List.hasDecEqₓ x y with
  | is_true p => is_true (congr_argₓ StringImp.mk p)
  | is_false p => is_false fun q => p (StringImp.mk.inj q)

def Empty : Stringₓ :=
  ⟨[]⟩

def length : Stringₓ → Nat
  | ⟨s⟩ => s.length

def push : Stringₓ → Charₓ → Stringₓ
  | ⟨s⟩, c => ⟨s ++ [c]⟩

def append : Stringₓ → Stringₓ → Stringₓ
  | ⟨a⟩, ⟨b⟩ => ⟨a ++ b⟩

def to_list : Stringₓ → List Charₓ
  | ⟨s⟩ => s

def fold {α} (a : α) (f : α → Charₓ → α) (s : Stringₓ) : α :=
  s.to_list.foldl f a

structure iterator_imp where
  fst : List Charₓ
  snd : List Charₓ

def iterator :=
  iterator_imp

def mk_iterator : Stringₓ → iterator
  | ⟨s⟩ => ⟨[], s⟩

namespace Iterator

def curr : iterator → Charₓ
  | ⟨p, c :: n⟩ => c
  | _ => default Charₓ

def set_curr : iterator → Charₓ → iterator
  | ⟨p, c :: n⟩, c' => ⟨p, c' :: n⟩
  | it, c' => it

def next : iterator → iterator
  | ⟨p, c :: n⟩ => ⟨c :: p, n⟩
  | ⟨p, []⟩ => ⟨p, []⟩

def prev : iterator → iterator
  | ⟨c :: p, n⟩ => ⟨p, c :: n⟩
  | ⟨[], n⟩ => ⟨[], n⟩

def has_next : iterator → Bool
  | ⟨p, []⟩ => ff
  | _ => tt

def has_prev : iterator → Bool
  | ⟨[], n⟩ => ff
  | _ => tt

def insert : iterator → Stringₓ → iterator
  | ⟨p, n⟩, ⟨s⟩ => ⟨p, s ++ n⟩

def remove : iterator → Nat → iterator
  | ⟨p, n⟩, m => ⟨p, n.drop m⟩

def to_string : iterator → Stringₓ
  | ⟨p, n⟩ => ⟨p.reverse ++ n⟩

def to_end : iterator → iterator
  | ⟨p, n⟩ => ⟨n.reverse ++ p, []⟩

def next_to_string : iterator → Stringₓ
  | ⟨p, n⟩ => ⟨n⟩

def prev_to_string : iterator → Stringₓ
  | ⟨p, n⟩ => ⟨p.reverse⟩

protected def extract_core : List Charₓ → List Charₓ → Option (List Charₓ)
  | [], cs => none
  | c :: cs₁, cs₂ =>
    if cs₁ = cs₂ then some [c]
    else
      match extract_core cs₁ cs₂ with
      | none => none
      | some r => some (c :: r)

def extract : iterator → iterator → Option Stringₓ
  | ⟨p₁, n₁⟩, ⟨p₂, n₂⟩ =>
    if p₁.reverse ++ n₁ ≠ p₂.reverse ++ n₂ then none
    else
      if n₁ = n₂ then some ""
      else
        match iterator.extract_core n₁ n₂ with
        | none => none
        | some r => some ⟨r⟩

end Iterator

end Stringₓ

instance : Inhabited Stringₓ :=
  ⟨Stringₓ.empty⟩

instance : SizeOf Stringₓ :=
  ⟨Stringₓ.length⟩

instance : Append Stringₓ :=
  ⟨Stringₓ.append⟩

namespace Stringₓ

def str : Stringₓ → Charₓ → Stringₓ :=
  push

def is_empty (s : Stringₓ) : Bool :=
  to_bool (s.length = 0)

def front (s : Stringₓ) : Charₓ :=
  s.mk_iterator.curr

def back (s : Stringₓ) : Charₓ :=
  s.mk_iterator.to_end.prev.curr

def join (l : List Stringₓ) : Stringₓ :=
  l.foldl (fun r s => r ++ s) ""

def singleton (c : Charₓ) : Stringₓ :=
  Empty.push c

def intercalate (s : Stringₓ) (ss : List Stringₓ) : Stringₓ :=
  (List.intercalate s.to_list (ss.map to_list)).asString

namespace Iterator

def nextn : iterator → Nat → iterator
  | it, 0 => it
  | it, i + 1 => nextn it.next i

def prevn : iterator → Nat → iterator
  | it, 0 => it
  | it, i + 1 => prevn it.prev i

end Iterator

def pop_back (s : Stringₓ) : Stringₓ :=
  s.mk_iterator.to_end.prev.prev_to_string

def popn_back (s : Stringₓ) (n : Nat) : Stringₓ :=
  (s.mk_iterator.to_end.prevn n).prevToString

def backn (s : Stringₓ) (n : Nat) : Stringₓ :=
  (s.mk_iterator.to_end.prevn n).nextToString

end Stringₓ

protected def Charₓ.toString (c : Charₓ) : Stringₓ :=
  Stringₓ.singleton c

private def to_nat_core : Stringₓ.Iterator → Nat → Nat → Nat
  | it, 0, r => r
  | it, i + 1, r =>
    let c := it.curr
    let r := r * 10 + c.to_nat - '0'.toNat
    to_nat_core it.next i r

def Stringₓ.toNat (s : Stringₓ) : Nat :=
  to_nat_core s.mk_iterator s.length 0

namespace Stringₓ

private theorem nil_ne_append_singleton : ∀ c : Charₓ l : List Charₓ, [] ≠ l ++ [c]
  | c, [] => fun h => List.noConfusion h
  | c, d :: l => fun h => List.noConfusion h

theorem empty_ne_str : ∀ c : Charₓ s : Stringₓ, Empty ≠ str s c
  | c, ⟨l⟩ => fun h : StringImp.mk [] = StringImp.mk (l ++ [c]) =>
    StringImp.noConfusion h $ fun h => nil_ne_append_singleton _ _ h

theorem str_ne_empty (c : Charₓ) (s : Stringₓ) : str s c ≠ Empty :=
  (empty_ne_str c s).symm

private theorem str_ne_str_left_aux : ∀ {c₁ c₂ : Charₓ} l₁ l₂ : List Charₓ, c₁ ≠ c₂ → l₁ ++ [c₁] ≠ l₂ ++ [c₂]
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

theorem str_ne_str_left : ∀ {c₁ c₂ : Charₓ} s₁ s₂ : Stringₓ, c₁ ≠ c₂ → str s₁ c₁ ≠ str s₂ c₂
  | c₁, c₂, StringImp.mk l₁, StringImp.mk l₂, h₁, h₂ =>
    have : l₁ ++ [c₁] = l₂ ++ [c₂] := StringImp.noConfusion h₂ id
    absurd this (str_ne_str_left_aux l₁ l₂ h₁)

private theorem str_ne_str_right_aux : ∀ c₁ c₂ : Charₓ {l₁ l₂ : List Charₓ}, l₁ ≠ l₂ → l₁ ++ [c₁] ≠ l₂ ++ [c₂]
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

theorem str_ne_str_right : ∀ c₁ c₂ : Charₓ {s₁ s₂ : Stringₓ}, s₁ ≠ s₂ → str s₁ c₁ ≠ str s₂ c₂
  | c₁, c₂, StringImp.mk l₁, StringImp.mk l₂, h₁, h₂ =>
    have aux : l₁ ≠ l₂ := fun h =>
      have : StringImp.mk l₁ = StringImp.mk l₂ := Eq.subst h rfl
      absurd this h₁
    have : l₁ ++ [c₁] = l₂ ++ [c₂] := StringImp.noConfusion h₂ id
    absurd this (str_ne_str_right_aux c₁ c₂ aux)

end Stringₓ

