/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Monad combinators, as in Haskell's Control.Monad.

! This file was ported from Lean 3 source module init.control.combinators
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Control.Monad
import Leanbin.Init.Control.Alternative
import Leanbin.Init.Data.List.Basic

universe u v w

#print List.mapM /-
def List.mapM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) :
    List α → m (List β)
  | [] => return []
  | h :: t => do
    let h' ← f h
    let t' ← List.mapM t
    return (h' :: t')
#align list.mmap List.mapM
-/

/- warning: list.mmap' -> List.mapM' is a dubious translation:
lean 3 declaration is
  forall {m : Type -> Type.{v}} [_inst_1 : Monad.{0, v} m] {α : Type.{u}} {β : Type}, (α -> (m β)) -> (List.{u} α) -> (m Unit)
but is expected to have type
  forall {m : Type.{u_1} -> Type.{u_2}} {_inst_1 : Type.{u_3}} {α : Type.{u_1}} [β : Monad.{u_1, u_2} m], (_inst_1 -> (m α)) -> (List.{u_3} _inst_1) -> (m (List.{u_1} α))
Case conversion may be inaccurate. Consider using '#align list.mmap' List.mapM'ₓ'. -/
def List.mapM' {m : Type → Type v} [Monad m] {α : Type u} {β : Type} (f : α → m β) : List α → m Unit
  | [] => return ()
  | h :: t => f h >> List.mapM' t
#align list.mmap' List.mapM'

#print joinM /-
def joinM {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
  bind a id
#align mjoin joinM
-/

#print List.filterM /-
def List.filterM {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) : List α → m (List α)
  | [] => return []
  | h :: t => do
    let b ← f h
    let t' ← List.filterM t
    cond b (return (h :: t')) (return t')
#align list.mfilter List.filterM
-/

#print List.foldlM /-
def List.foldlM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} :
    (s → α → m s) → s → List α → m s
  | f, s, [] => return s
  | f, s, h :: r => do
    let s' ← f s h
    List.foldlM f s' r
#align list.mfoldl List.foldlM
-/

#print List.foldrM /-
def List.foldrM {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} :
    (α → s → m s) → s → List α → m s
  | f, s, [] => return s
  | f, s, h :: r => do
    let s' ← List.foldrM f s r
    f h s'
#align list.mfoldr List.foldrM
-/

#print List.firstM /-
def List.firstM {m : Type u → Type v} [Monad m] [Alternative m] {α : Type w} {β : Type u}
    (f : α → m β) : List α → m β
  | [] => failure
  | a :: as => f a <|> List.firstM as
#align list.mfirst List.firstM
-/

#print when /-
def when {m : Type → Type} [Monad m] (c : Prop) [h : Decidable c] (t : m Unit) : m Unit :=
  ite c t (pure ())
#align when when
-/

#print condM /-
def condM {m : Type → Type} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α := do
  let b ← mbool
  cond b tm fm
#align mcond condM
-/

#print whenM /-
def whenM {m : Type → Type} [Monad m] (c : m Bool) (t : m Unit) : m Unit :=
  condM c t (return ())
#align mwhen whenM
-/

export List (mmap mmap' mfilter mfoldl)

namespace Monad

#print Monad.mapM /-
def mapM :=
  @mapM
#align monad.mapm Monad.mapM
-/

/- warning: monad.mapm' -> Monad.mapM' is a dubious translation:
lean 3 declaration is
  forall {m : Type -> Type.{u_1}} [_inst_1 : Monad.{0, u_1} m] {α : Type.{u_2}} {β : Type}, (α -> (m β)) -> (List.{u_2} α) -> (m Unit)
but is expected to have type
  forall {m : Type.{u_1} -> Type.{u_2}} {_inst_1 : Type.{u_3}} {α : Type.{u_1}} [β : Monad.{u_1, u_2} m], (_inst_1 -> (m α)) -> (List.{u_3} _inst_1) -> (m (List.{u_1} α))
Case conversion may be inaccurate. Consider using '#align monad.mapm' Monad.mapM'ₓ'. -/
def mapM' :=
  @mapM'
#align monad.mapm' Monad.mapM'

#print Monad.join /-
def join :=
  @joinM
#align monad.join Monad.join
-/

#print Monad.filter /-
def filter :=
  @filterM
#align monad.filter Monad.filter
-/

#print Monad.foldl /-
def foldl :=
  @foldlM
#align monad.foldl Monad.foldl
-/

#print Monad.cond /-
def cond :=
  @condM
#align monad.cond Monad.cond
-/

#print Monad.sequence /-
def sequence {m : Type u → Type v} [Monad m] {α : Type u} : List (m α) → m (List α)
  | [] => return []
  | h :: t => do
    let h' ← h
    let t' ← sequence t
    return (h' :: t')
#align monad.sequence Monad.sequence
-/

#print Monad.sequence' /-
def sequence' {m : Type → Type u} [Monad m] {α : Type} : List (m α) → m Unit
  | [] => return ()
  | h :: t => h >> sequence' t
#align monad.sequence' Monad.sequence'
-/

#print Monad.whenb /-
def whenb {m : Type → Type} [Monad m] (b : Bool) (t : m Unit) : m Unit :=
  cond b t (return ())
#align monad.whenb Monad.whenb
-/

#print Monad.unlessb /-
def unlessb {m : Type → Type} [Monad m] (b : Bool) (t : m Unit) : m Unit :=
  cond b (return ()) t
#align monad.unlessb Monad.unlessb
-/

end Monad

