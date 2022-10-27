/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Leanbin.Init.Control.Functor

open Function

universe u v

class Pure (f : Type u → Type v) where
  pure {α : Type u} : α → f α

export Pure (pure)

class Seq (f : Type u → Type v) : Type max (u + 1) v where
  seq : ∀ {α β : Type u}, f (α → β) → f α → f β

class SeqLeft (f : Type u → Type v) : Type max (u + 1) v where
  seqLeft : ∀ {α β : Type u}, f α → f β → f α

class SeqRight (f : Type u → Type v) : Type max (u + 1) v where
  seqRight : ∀ {α β : Type u}, f α → f β → f β

class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map := fun _ _ x y => pure x <*> y
  seqLeft := fun α β a b => const β <$> a <*> b
  seqRight := fun α β a b => const α id <$> a <*> b

