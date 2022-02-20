/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
prelude
import Leanbin.Init.Data.Ordering.Basic
import Leanbin.Init.Function
import Leanbin.Init.Meta.Name
import Leanbin.Init.Meta.Format
import Leanbin.Init.Control.Monad

open Format

private unsafe def format_key {key} [has_to_format key] (k : key) (first : Bool) : format :=
  (if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt k

namespace Native

unsafe axiom rb_map.{u₁, u₂} : Type u₁ → Type u₂ → Type max u₁ u₂

namespace RbMap

unsafe axiom mk_core {key : Type} (data : Type) : (key → key → Ordering) → rb_map key data

unsafe axiom size {key : Type} {data : Type} : rb_map key data → Nat

unsafe axiom empty {key : Type} {data : Type} : rb_map key data → Bool

unsafe axiom insert {key : Type} {data : Type} : rb_map key data → key → data → rb_map key data

unsafe axiom erase {key : Type} {data : Type} : rb_map key data → key → rb_map key data

unsafe axiom contains {key : Type} {data : Type} : rb_map key data → key → Bool

unsafe axiom find {key : Type} {data : Type} : rb_map key data → key → Option data

unsafe axiom min {key : Type} {data : Type} : rb_map key data → Option data

unsafe axiom max {key : Type} {data : Type} : rb_map key data → Option data

unsafe axiom fold {key : Type} {data : Type} {α : Type} : rb_map key data → α → (key → data → α → α) → α

@[inline]
unsafe def mk (key : Type) [LT key] [DecidableRel ((· < ·) : key → key → Prop)] (data : Type) : rb_map key data :=
  mk_core data cmp

open List

section

variable {key data : Type}

unsafe def keys (m : rb_map key data) : List key :=
  fold m [] fun k v ks => k :: ks

unsafe def values {key : Type} {data : Type} (m : rb_map key data) : List data :=
  fold m [] fun k v vs => v :: vs

unsafe def to_list {key : Type} {data : Type} (m : rb_map key data) : List (key × data) :=
  fold m [] fun k v res => (k, v) :: res

unsafe def mfold {key data α : Type} {m : Type → Type} [Monadₓ m] (mp : rb_map key data) (a : α)
    (fn : key → data → α → m α) : m α :=
  mp.fold (return a) fun k d act => act >>= fn k d

end

section

variable {key data data' : Type} [LT key] [DecidableRel ((· < ·) : key → key → Prop)]

unsafe def of_list : List (key × data) → rb_map key data
  | [] => mk key data
  | (k, v) :: ls => insert (of_list ls) k v

unsafe def set_of_list : List key → rb_map key Unit
  | [] => mk _ _
  | x :: xs => insert (set_of_list xs) x ()

unsafe def map (f : data → data') (m : rb_map key data) : rb_map key data' :=
  fold m (mk _ _) fun k v res => insert res k (f v)

unsafe def for (m : rb_map key data) (f : data → data') : rb_map key data' :=
  map f m

unsafe def filter (m : rb_map key data) (f : data → Prop) [DecidablePred f] :=
  (fold m (mk _ _)) fun a b m' => if f b then insert m' a b else m'

end

end RbMap

unsafe def mk_rb_map {key data : Type} [LT key] [DecidableRel ((· < ·) : key → key → Prop)] : rb_map key data :=
  rb_map.mk key data

@[reducible]
unsafe def nat_map (data : Type) :=
  rb_map Nat data

namespace NatMap

export
  RbMap (mk_core size Empty insert erase contains find min max fold keys values toList mfold of_list set_of_list map for filter)

unsafe def mk (data : Type) : nat_map data :=
  rb_map.mk Nat data

end NatMap

unsafe def mk_nat_map {data : Type} : nat_map data :=
  nat_map.mk data

open RbMap Prod

section

variable {key : Type} {data : Type} [has_to_format key] [has_to_format data]

private unsafe def format_key_data (k : key) (d : data) (first : Bool) : format :=
  (if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt k ++ space ++ to_fmt "←" ++ space ++ to_fmt d

unsafe instance : has_to_format (rb_map key data) :=
  ⟨fun m =>
    group <|
      to_fmt "⟨" ++
          nest 1 (fst (fold m (to_fmt "", true) fun k d p => (fst p ++ format_key_data k d (snd p), false))) ++
        to_fmt "⟩"⟩

end

section

variable {key : Type} {data : Type} [HasToString key] [HasToString data]

private unsafe def key_data_to_string (k : key) (d : data) (first : Bool) : Stringₓ :=
  (if first then "" else ", ") ++ toString k ++ " ← " ++ toString d

unsafe instance : HasToString (rb_map key data) :=
  ⟨fun m => "⟨" ++ fst (fold m ("", true) fun k d p => (fst p ++ key_data_to_string k d (snd p), false)) ++ "⟩"⟩

end

/-- a variant of rb_maps that stores a list of elements for each key.
   `find` returns the list of elements in the opposite order that they were inserted. -/
unsafe def rb_lmap (key : Type) (data : Type) : Type :=
  rb_map key (List data)

namespace RbLmap

protected unsafe def mk (key : Type) [LT key] [DecidableRel ((· < ·) : key → key → Prop)] (data : Type) :
    rb_lmap key data :=
  rb_map.mk key (List data)

unsafe def insert {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) (d : data) : rb_lmap key data :=
  match rb_map.find rbl k with
  | none => rb_map.insert rbl k [d]
  | some l => rb_map.insert (rb_map.erase rbl k) k (d :: l)

unsafe def erase {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) : rb_lmap key data :=
  rb_map.erase rbl k

unsafe def contains {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) : Bool :=
  rb_map.contains rbl k

unsafe def find {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) : List data :=
  match rb_map.find rbl k with
  | none => []
  | some l => l

end RbLmap

unsafe def rb_set key :=
  rb_map key Unit

unsafe def mk_rb_set {key} [LT key] [DecidableRel ((· < ·) : key → key → Prop)] : rb_set key :=
  mk_rb_map

namespace RbSet

unsafe def insert {key} (s : rb_set key) (k : key) : rb_set key :=
  rb_map.insert s k ()

unsafe def erase {key} (s : rb_set key) (k : key) : rb_set key :=
  rb_map.erase s k

unsafe def contains {key} (s : rb_set key) (k : key) : Bool :=
  rb_map.contains s k

unsafe def size {key} (s : rb_set key) : Nat :=
  rb_map.size s

unsafe def empty {key : Type} (s : rb_set key) : Bool :=
  rb_map.empty s

unsafe def fold {key α : Type} (s : rb_set key) (a : α) (fn : key → α → α) : α :=
  rb_map.fold s a fun k _ a => fn k a

unsafe def mfold {key α : Type} {m : Type → Type} [Monadₓ m] (s : rb_set key) (a : α) (fn : key → α → m α) : m α :=
  s.fold (return a) fun k act => act >>= fn k

unsafe def to_list {key : Type} (s : rb_set key) : List key :=
  s.fold [] List.cons

unsafe instance {key} [has_to_format key] : has_to_format (rb_set key) :=
  ⟨fun m =>
    group <|
      to_fmt "{" ++ nest 1 (fst (fold m (to_fmt "", true) fun k p => (fst p ++ format_key k (snd p), false))) ++
        to_fmt "}"⟩

end RbSet

end Native

open Native

@[reducible]
unsafe def name_map (data : Type) :=
  rb_map Name data

namespace NameMap

export
  Native.RbMap (mk_core size Empty insert erase contains find min max fold keys values toList mfold of_list set_of_list map for filter)

unsafe def mk (data : Type) : name_map data :=
  rb_map.mk_core data name.cmp

end NameMap

unsafe def mk_name_map {data : Type} : name_map data :=
  name_map.mk data

/-- An rb_map of `name`s. -/
unsafe axiom name_set : Type

unsafe axiom mk_name_set : name_set

namespace NameSet

unsafe axiom insert : name_set → Name → name_set

unsafe axiom erase : name_set → Name → name_set

unsafe axiom contains : name_set → Name → Bool

unsafe axiom size : name_set → Nat

unsafe axiom empty : name_set → Bool

unsafe axiom fold {α : Type} : name_set → α → (Name → α → α) → α

unsafe def union (l r : name_set) : name_set :=
  r.fold l fun ns n => name_set.insert n ns

unsafe def to_list (s : name_set) : List Name :=
  s.fold [] List.cons

unsafe instance : has_to_format name_set :=
  ⟨fun m =>
    group <|
      to_fmt "{" ++ nest 1 (fold m (to_fmt "", true) fun k p => (p.1 ++ format_key k p.2, false)).1 ++ to_fmt "}"⟩

unsafe def of_list (l : List Name) : name_set :=
  List.foldlₓ name_set.insert mk_name_set l

unsafe def mfold {α : Type} {m : Type → Type} [Monadₓ m] (ns : name_set) (a : α) (fn : Name → α → m α) : m α :=
  ns.fold (return a) fun k act => act >>= fn k

end NameSet

