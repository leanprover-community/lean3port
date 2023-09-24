/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Lift
import Init.Data.String.Basic

#align_import init.control.monad_fail from "leanprover-community/lean"@"9af482290ef68e8aaa5ead01aa7b09b7be7019fd"

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

