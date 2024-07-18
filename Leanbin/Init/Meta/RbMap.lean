/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
prelude
import Init.Data.Ordering.Basic
import Logic.Function.Defs
import Init.Meta.Name
import Init.Meta.Format
import Init.Control.Monad

#align_import init.meta.rb_map from "leanprover-community/lean"@"a880838c40c42543e5da9283c1eb587e52bce6c5"

open Format

private unsafe def format_key {key} [has_to_format key] (k : key) (first : Bool) : format :=
  (if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt k

namespace Native

unsafe axiom rb_map.{u₁, u₂} : Type u₁ → Type u₂ → Type max u₁ u₂
#align native.rb_map native.rb_map

namespace RbMap

unsafe axiom mk_core {key : Type} (data : Type) : (key → key → Ordering) → rb_map key data
#align native.rb_map.mk_core native.rb_map.mk_core

unsafe axiom size {key : Type} {data : Type} : rb_map key data → Nat
#align native.rb_map.size native.rb_map.size

unsafe axiom empty {key : Type} {data : Type} : rb_map key data → Bool
#align native.rb_map.empty native.rb_map.empty

unsafe axiom insert {key : Type} {data : Type} : rb_map key data → key → data → rb_map key data
#align native.rb_map.insert native.rb_map.insert

unsafe axiom erase {key : Type} {data : Type} : rb_map key data → key → rb_map key data
#align native.rb_map.erase native.rb_map.erase

unsafe axiom contains {key : Type} {data : Type} : rb_map key data → key → Bool
#align native.rb_map.contains native.rb_map.contains

unsafe axiom find {key : Type} {data : Type} : rb_map key data → key → Option data
#align native.rb_map.find native.rb_map.find

unsafe axiom min {key : Type} {data : Type} : rb_map key data → Option data
#align native.rb_map.min native.rb_map.min

unsafe axiom max {key : Type} {data : Type} : rb_map key data → Option data
#align native.rb_map.max native.rb_map.max

unsafe axiom fold {key : Type} {data : Type} {α : Type} :
    rb_map key data → α → (key → data → α → α) → α
#align native.rb_map.fold native.rb_map.fold

@[inline]
unsafe def mk (key : Type) [LT key] [DecidableRel ((· < ·) : key → key → Prop)] (data : Type) :
    rb_map key data :=
  mk_core data cmp
#align native.rb_map.mk native.rb_map.mk

open List

section

variable {key data : Type}

unsafe def keys (m : rb_map key data) : List key :=
  fold m [] fun k v ks => k :: ks
#align native.rb_map.keys native.rb_map.keys

unsafe def values {key : Type} {data : Type} (m : rb_map key data) : List data :=
  fold m [] fun k v vs => v :: vs
#align native.rb_map.values native.rb_map.values

unsafe def to_list {key : Type} {data : Type} (m : rb_map key data) : List (key × data) :=
  fold m [] fun k v res => (k, v) :: res
#align native.rb_map.to_list native.rb_map.to_list

unsafe def mfold {key data α : Type} {m : Type → Type} [Monad m] (mp : rb_map key data) (a : α)
    (fn : key → data → α → m α) : m α :=
  mp.fold (return a) fun k d act => act >>= fn k d
#align native.rb_map.mfold native.rb_map.mfold

end

section

variable {key data data' : Type} [LT key] [DecidableRel ((· < ·) : key → key → Prop)]

unsafe def of_list : List (key × data) → rb_map key data
  | [] => mk key data
  | (k, v) :: ls => insert (of_list ls) k v
#align native.rb_map.of_list native.rb_map.of_list

unsafe def set_of_list : List key → rb_map key Unit
  | [] => mk _ _
  | x :: xs => insert (set_of_list xs) x ()
#align native.rb_map.set_of_list native.rb_map.set_of_list

unsafe def map (f : data → data') (m : rb_map key data) : rb_map key data' :=
  fold m (mk _ _) fun k v res => insert res k (f v)
#align native.rb_map.map native.rb_map.map

unsafe def for (m : rb_map key data) (f : data → data') : rb_map key data' :=
  map f m
#align native.rb_map.for native.rb_map.for

unsafe def filter (m : rb_map key data) (f : data → Prop) [DecidablePred f] :=
  fold m (mk _ _) fun a b m' => if f b then insert m' a b else m'
#align native.rb_map.filter native.rb_map.filter

end

end RbMap

unsafe def mk_rb_map {key data : Type} [LT key] [DecidableRel ((· < ·) : key → key → Prop)] :
    rb_map key data :=
  rb_map.mk key data
#align native.mk_rb_map native.mk_rb_map

@[reducible]
unsafe def nat_map (data : Type) :=
  rb_map Nat data
#align native.nat_map native.nat_map

namespace NatMap

export
  RbMap (mk_core size Empty insert eraseₓ contains find min max fold keys values toList mfold of_list set_of_list map for filterₓ)

unsafe def mk (data : Type) : nat_map data :=
  rb_map.mk Nat data
#align native.nat_map.mk native.nat_map.mk

end NatMap

unsafe def mk_nat_map {data : Type} : nat_map data :=
  nat_map.mk data
#align native.mk_nat_map native.mk_nat_map

open RbMap Prod

section

variable {key : Type} {data : Type} [has_to_format key] [has_to_format data]

private unsafe def format_key_data (k : key) (d : data) (first : Bool) : format :=
  (if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt k ++ space ++ to_fmt "←" ++ space ++
    to_fmt d

unsafe instance : has_to_format (rb_map key data) :=
  ⟨fun m =>
    group <|
      to_fmt "⟨" ++
          nest 1
            (fst
              (fold m (to_fmt "", true) fun k d p =>
                (fst p ++ format_key_data k d (snd p), false))) ++
        to_fmt "⟩"⟩

end

section

variable {key : Type} {data : Type} [ToString key] [ToString data]

private unsafe def key_data_to_string (k : key) (d : data) (first : Bool) : String :=
  (if first then "" else ", ") ++ toString k ++ " ← " ++ toString d

unsafe instance : ToString (rb_map key data) :=
  ⟨fun m =>
    "⟨" ++ fst (fold m ("", true) fun k d p => (fst p ++ key_data_to_string k d (snd p), false)) ++
      "⟩"⟩

end

/-- a variant of rb_maps that stores a list of elements for each key.
   `find` returns the list of elements in the opposite order that they were inserted. -/
unsafe def rb_lmap (key : Type) (data : Type) : Type :=
  rb_map key (List data)
#align native.rb_lmap native.rb_lmap

namespace RbLmap

protected unsafe def mk (key : Type) [LT key] [DecidableRel ((· < ·) : key → key → Prop)]
    (data : Type) : rb_lmap key data :=
  rb_map.mk key (List data)
#align native.rb_lmap.mk native.rb_lmap.mk

unsafe def insert {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) (d : data) :
    rb_lmap key data :=
  match rb_map.find rbl k with
  | none => rb_map.insert rbl k [d]
  | some l => rb_map.insert (rb_map.erase rbl k) k (d :: l)
#align native.rb_lmap.insert native.rb_lmap.insert

unsafe def erase {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) : rb_lmap key data :=
  rb_map.erase rbl k
#align native.rb_lmap.erase native.rb_lmap.erase

unsafe def contains {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) : Bool :=
  rb_map.contains rbl k
#align native.rb_lmap.contains native.rb_lmap.contains

unsafe def find {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) : List data :=
  match rb_map.find rbl k with
  | none => []
  | some l => l
#align native.rb_lmap.find native.rb_lmap.find

end RbLmap

unsafe def rb_set (key) :=
  rb_map key Unit
#align native.rb_set native.rb_set

unsafe def mk_rb_set {key} [LT key] [DecidableRel ((· < ·) : key → key → Prop)] : rb_set key :=
  mk_rb_map
#align native.mk_rb_set native.mk_rb_set

namespace RbSet

unsafe def insert {key} (s : rb_set key) (k : key) : rb_set key :=
  rb_map.insert s k ()
#align native.rb_set.insert native.rb_set.insert

unsafe def erase {key} (s : rb_set key) (k : key) : rb_set key :=
  rb_map.erase s k
#align native.rb_set.erase native.rb_set.erase

unsafe def contains {key} (s : rb_set key) (k : key) : Bool :=
  rb_map.contains s k
#align native.rb_set.contains native.rb_set.contains

unsafe def size {key} (s : rb_set key) : Nat :=
  rb_map.size s
#align native.rb_set.size native.rb_set.size

unsafe def empty {key : Type} (s : rb_set key) : Bool :=
  rb_map.empty s
#align native.rb_set.empty native.rb_set.empty

unsafe def fold {key α : Type} (s : rb_set key) (a : α) (fn : key → α → α) : α :=
  rb_map.fold s a fun k _ a => fn k a
#align native.rb_set.fold native.rb_set.fold

unsafe def mfold {key α : Type} {m : Type → Type} [Monad m] (s : rb_set key) (a : α)
    (fn : key → α → m α) : m α :=
  s.fold (return a) fun k act => act >>= fn k
#align native.rb_set.mfold native.rb_set.mfold

unsafe def to_list {key : Type} (s : rb_set key) : List key :=
  s.fold [] List.cons
#align native.rb_set.to_list native.rb_set.to_list

unsafe instance {key} [has_to_format key] : has_to_format (rb_set key) :=
  ⟨fun m =>
    group <|
      to_fmt "{" ++
          nest 1
            (fst (fold m (to_fmt "", true) fun k p => (fst p ++ format_key k (snd p), false))) ++
        to_fmt "}"⟩

end RbSet

end Native

open Native

@[reducible]
unsafe def name_map (data : Type) :=
  rb_map Name data
#align name_map name_map

namespace NameMap

export
  Native.RbMap (mk_core size Empty insert eraseₓ contains find min max fold keys values toList mfold of_list set_of_list map for filterₓ)

unsafe def mk (data : Type) : name_map data :=
  rb_map.mk_core data name.cmp
#align name_map.mk name_map.mk

end NameMap

unsafe def mk_name_map {data : Type} : name_map data :=
  name_map.mk data
#align mk_name_map mk_name_map

/-- An rb_map of `name`s. -/
unsafe axiom name_set : Type
#align name_set name_set

unsafe axiom mk_name_set : name_set
#align mk_name_set mk_name_set

namespace NameSet

unsafe axiom insert : name_set → Name → name_set
#align name_set.insert name_set.insert

unsafe axiom erase : name_set → Name → name_set
#align name_set.erase name_set.erase

unsafe axiom contains : name_set → Name → Bool
#align name_set.contains name_set.contains

unsafe axiom size : name_set → Nat
#align name_set.size name_set.size

unsafe axiom empty : name_set → Bool
#align name_set.empty name_set.empty

unsafe axiom fold {α : Type} : name_set → α → (Name → α → α) → α
#align name_set.fold name_set.fold

unsafe def union (l r : name_set) : name_set :=
  r.fold l fun ns n => name_set.insert n ns
#align name_set.union name_set.union

unsafe def to_list (s : name_set) : List Name :=
  s.fold [] List.cons
#align name_set.to_list name_set.to_list

unsafe instance : has_to_format name_set :=
  ⟨fun m =>
    group <|
      to_fmt "{" ++
          nest 1 (fold m (to_fmt "", true) fun k p => (p.1 ++ format_key k p.2, false)).1 ++
        to_fmt "}"⟩

unsafe def of_list (l : List Name) : name_set :=
  List.foldl name_set.insert mk_name_set l
#align name_set.of_list name_set.of_list

unsafe def mfold {α : Type} {m : Type → Type} [Monad m] (ns : name_set) (a : α)
    (fn : Name → α → m α) : m α :=
  ns.fold (return a) fun k act => act >>= fn k
#align name_set.mfold name_set.mfold

end NameSet

