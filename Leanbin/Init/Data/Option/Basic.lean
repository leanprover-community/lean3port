prelude
import Leanbin.Init.Logic
import Leanbin.Init.Control.Monad
import Leanbin.Init.Control.Alternative

open Decidable

universe u v

namespace Option

def to_monad {m : Type → Type} [Monadₓ m] [Alternativeₓ m] {A} : Option A → m A
  | none => failure
  | some a => return a

def get_or_else {α : Type u} : Option α → α → α
  | some x, _ => x
  | none, e => e

def is_some {α : Type u} : Option α → Bool
  | some _ => tt
  | none => ff

def is_none {α : Type u} : Option α → Bool
  | some _ => ff
  | none => tt

def get {α : Type u} : ∀ {o : Option α}, is_some o → α
  | some x, h => x
  | none, h => False.ndrec _ $ Bool.ff_ne_tt h

def rhoare {α : Type u} : Bool → α → Option α
  | tt, a => none
  | ff, a => some a

def lhoare {α : Type u} : α → Option α → α
  | a, none => a
  | _, some b => b

infixr:1 "|>" => rhoare

infixr:1 "<|" => lhoare

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
  | none, none => is_true rfl
  | none, some v₂ => is_false fun h => Option.noConfusion h
  | some v₁, none => is_false fun h => Option.noConfusion h
  | some v₁, some v₂ =>
    match d v₁ v₂ with
    | is_true e => is_true (congr_argₓ (@some α) e)
    | is_false n => is_false fun h => Option.noConfusion h fun e => absurd e n

