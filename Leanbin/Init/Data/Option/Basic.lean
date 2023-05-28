/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.option.basic
! leanprover-community/lean commit e611ee5c2bd410148bcd493c58cb17498d667175
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Control.Monad
import Leanbin.Init.Control.Alternative

open Decidable

universe u v

namespace Option

def toMonad {m : Type → Type} [Monad m] [Alternative m] {A} : Option A → m A
  | none => failure
  | some a => return a
#align option.to_monad Option.toMonad

#print Option.getD /-
def getD {α : Type u} : Option α → α → α
  | some x, _ => x
  | none, e => e
#align option.get_or_else Option.getD
-/

#print Option.isSome /-
def isSome {α : Type u} : Option α → Bool
  | some _ => true
  | none => false
#align option.is_some Option.isSome
-/

#print Option.isNone /-
def isNone {α : Type u} : Option α → Bool
  | some _ => false
  | none => true
#align option.is_none Option.isNone
-/

#print Option.get /-
def get {α : Type u} : ∀ {o : Option α}, isSome o → α
  | some x, h => x
  | none, h => False.ndrec _ <| Bool.false_ne_true h
#align option.get Option.get
-/

def rhoare {α : Type u} : Bool → α → Option α
  | tt, a => none
  | ff, a => some a
#align option.rhoare Option.rhoare

def lhoare {α : Type u} : α → Option α → α
  | a, none => a
  | _, some b => b
#align option.lhoare Option.lhoare

#print Option.bind /-
@[inline]
protected def bind {α : Type u} {β : Type v} : Option α → (α → Option β) → Option β
  | none, b => none
  | some a, b => b a
#align option.bind Option.bind
-/

#print Option.map /-
protected def map {α β} (f : α → β) (o : Option α) : Option β :=
  Option.bind o (some ∘ f)
#align option.map Option.map
-/

#print Option.map_id /-
theorem map_id {α} : (Option.map id : Option α → Option α) = id :=
  funext fun o =>
    match o with
    | none => rfl
    | some x => rfl
#align option.map_id Option.map_id
-/

instance : Monad Option where
  pure := @some
  bind := @Option.bind
  map := @Option.map

protected def orelse {α : Type u} : Option α → Option α → Option α
  | some a, o => some a
  | none, some a => some a
  | none, none => none
#align option.orelse Option.orelse

instance : Alternative Option where
  failure := @none
  orelse := @Option.orelse

end Option

instance (α : Type u) : Inhabited (Option α) :=
  ⟨none⟩

instance {α : Type u} [d : DecidableEq α] : DecidableEq (Option α)
  | none, none => isTrue rfl
  | none, some v₂ => isFalse fun h => Option.noConfusion h
  | some v₁, none => isFalse fun h => Option.noConfusion h
  | some v₁, some v₂ =>
    match d v₁ v₂ with
    | is_true e => isTrue (congr_arg (@some α) e)
    | is_false n => isFalse fun h => Option.noConfusion h fun e => absurd e n

