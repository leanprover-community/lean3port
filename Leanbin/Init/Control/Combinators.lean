/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Monad combinators, as in Haskell's Control.Monad.
-/
prelude
import Leanbin.Init.Control.Monad
import Leanbin.Init.Control.Alternative
import Leanbin.Init.Data.List.Basic

universe u v w

def List.mmapₓ {m : Type u → Type v} [Monadₓ m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β)
  | [] => return []
  | h :: t => do
    let h' ← f h
    let t' ← List.mmapₓ t
    return (h' :: t')

def List.mmap'ₓ {m : Type → Type v} [Monadₓ m] {α : Type u} {β : Type} (f : α → m β) : List α → m Unit
  | [] => return ()
  | h :: t => f h >> List.mmap'ₓ t

def mjoin {m : Type u → Type u} [Monadₓ m] {α : Type u} (a : m (m α)) : m α :=
  bind a id

def List.mfilter {m : Type → Type v} [Monadₓ m] {α : Type} (f : α → m Bool) : List α → m (List α)
  | [] => return []
  | h :: t => do
    let b ← f h
    let t' ← List.mfilter t
    cond b (return (h :: t')) (return t')

def List.mfoldl {m : Type u → Type v} [Monadₓ m] {s : Type u} {α : Type w} : (s → α → m s) → s → List α → m s
  | f, s, [] => return s
  | f, s, h :: r => do
    let s' ← f s h
    List.mfoldl f s' r

def List.mfoldr {m : Type u → Type v} [Monadₓ m] {s : Type u} {α : Type w} : (α → s → m s) → s → List α → m s
  | f, s, [] => return s
  | f, s, h :: r => do
    let s' ← List.mfoldr f s r
    f h s'

def List.mfirstₓ {m : Type u → Type v} [Monadₓ m] [Alternativeₓ m] {α : Type w} {β : Type u} (f : α → m β) :
    List α → m β
  | [] => failure
  | a :: as => f a <|> List.mfirstₓ as

def when {m : Type → Type} [Monadₓ m] (c : Prop) [h : Decidable c] (t : m Unit) : m Unit :=
  ite c t (pure ())

def mcond {m : Type → Type} [Monadₓ m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α := do
  let b ← mbool
  cond b tm fm

def mwhen {m : Type → Type} [Monadₓ m] (c : m Bool) (t : m Unit) : m Unit :=
  mcond c t (return ())

export List (mmap mmap' mfilter mfoldl)

namespace Monadₓ

def mapm :=
  @mmapₓ

def mapm' :=
  @mmap'ₓ

def join :=
  @mjoin

def filter :=
  @mfilter

def foldl :=
  @mfoldl

def cond :=
  @mcond

def sequence {m : Type u → Type v} [Monadₓ m] {α : Type u} : List (m α) → m (List α)
  | [] => return []
  | h :: t => do
    let h' ← h
    let t' ← sequence t
    return (h' :: t')

def sequence' {m : Type → Type u} [Monadₓ m] {α : Type} : List (m α) → m Unit
  | [] => return ()
  | h :: t => h >> sequence' t

def whenb {m : Type → Type} [Monadₓ m] (b : Bool) (t : m Unit) : m Unit :=
  cond b t (return ())

def unlessb {m : Type → Type} [Monadₓ m] (b : Bool) (t : m Unit) : m Unit :=
  cond b (return ()) t

end Monadₓ

