/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.control.monad_fail
! leanprover-community/mathlib commit 9af482290ef68e8aaa5ead01aa7b09b7be7019fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Control.Lift
import Leanbin.Init.Data.String.Basic

universe u v

class MonadFail (m : Type u → Type v) where
  fail : ∀ {a}, String → m a
#align monad_fail MonadFail

def matchFailed {α : Type u} {m : Type u → Type v} [MonadFail m] : m α :=
  MonadFail.fail "match failed"
#align match_failed matchFailed

instance (priority := 100) monadFailLift (m n : Type u → Type v) [Monad n] [MonadFail m]
    [HasMonadLift m n] : MonadFail n where fail α s := monadLift (MonadFail.fail s : m α)
#align monad_fail_lift monadFailLift

