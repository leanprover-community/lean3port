/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Control.Monad
import Leanbin.Init.Control.Alternative

open Decidable

universe u v

namespace Option

def toMonadₓ {m : Type → Type} [Monadₓ m] [Alternativeₓ m] {A} : Option A → m A
  | none => failure
  | some a => return a

def getOrElse {α : Type u} : Option α → α → α
  | some x, _ => x
  | none, e => e

def isSome {α : Type u} : Option α → Bool
  | some _ => true
  | none => false

def isNone {α : Type u} : Option α → Bool
  | some _ => false
  | none => true

def getₓ {α : Type u} : ∀ {o : Option α}, isSome o → α
  | some x, h => x
  | none, h => False.ndrec _ <| Bool.ff_ne_tt h

def rhoare {α : Type u} : Bool → α → Option α
  | tt, a => none
  | ff, a => some a

def lhoare {α : Type u} : α → Option α → α
  | a, none => a
  | _, some b => b

@[inline]
protected def bind {α : Type u} {β : Type v} : Option α → (α → Option β) → Option β
  | none, b => none
  | some a, b => b a

protected def map {α β} (f : α → β) (o : Option α) : Option β :=
  Option.bind o (some ∘ f)

theorem map_id {α} : (Option.map id : Option α → Option α) = id :=
  funext fun o =>
    match o with
    | none => rfl
    | some x => rfl

instance : Monadₓ Option where
  pure := @some
  bind := @Option.bind
  map := @Option.map

protected def orelse {α : Type u} : Option α → Option α → Option α
  | some a, o => some a
  | none, some a => some a
  | none, none => none

instance : Alternativeₓ Option where
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

