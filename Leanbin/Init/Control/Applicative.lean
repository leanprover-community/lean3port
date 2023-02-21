/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

! This file was ported from Lean 3 source module init.control.applicative
! leanprover-community/mathlib commit e611ee5c2bd410148bcd493c58cb17498d667175
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Control.Functor

open Function

universe u v

#print Pure /-
class Pure (f : Type u → Type v) where
  pure {α : Type u} : α → f α
#align has_pure Pure
-/

export Pure (pure)

#print Seq /-
class Seq (f : Type u → Type v) : Type max (u + 1) v where
  seq : ∀ {α β : Type u}, f (α → β) → f α → f β
#align has_seq Seq
-/

#print SeqLeft /-
class SeqLeft (f : Type u → Type v) : Type max (u + 1) v where
  seqLeft : ∀ {α β : Type u}, f α → f β → f α
#align has_seq_left SeqLeft
-/

#print SeqRight /-
class SeqRight (f : Type u → Type v) : Type max (u + 1) v where
  seqRight : ∀ {α β : Type u}, f α → f β → f β
#align has_seq_right SeqRight
-/

#print Applicative /-
class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f,
  SeqRight f where
  map := fun _ _ x y => pure x <*> y
  seqLeft := fun α β a b => const β <$> a <*> b
  seqRight := fun α β a b => const α id <$> a <*> b
#align applicative Applicative
-/

