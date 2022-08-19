/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich

Classy functions for lifting monadic actions of different shapes.

This theory is roughly modeled after the Haskell 'layers' package https://hackage.haskell.org/package/layers-0.1.
Please see https://hackage.haskell.org/package/layers-0.1/docs/Documentation-Layers-Overview.html for an exhaustive discussion of the different approaches to lift functions.
-/
prelude
import Leanbin.Init.Function
import Leanbin.Init.Coe
import Leanbin.Init.Control.Monad

universe u v w

abbrev HasMonadLift := MonadLift
abbrev HasMonadLiftT := MonadLiftT

@[simp]
theorem monad_lift_refl {m : Type u → Type v} {α} : (monadLift : m α → m α) = id :=
  rfl

/-- Run a monad stack to completion.
    `run` should be the composition of the transformers' individual `run` functions.
    This class mostly saves some typing when using highly nested monad stacks:
    ```
    @[reducible] def my_monad := reader_t my_cfg $ state_t my_state $ except_t my_err id
    -- def my_monad.run {α : Type} (x : my_monad α) (cfg : my_cfg) (st : my_state) := ((x.run cfg).run st).run
    def my_monad.run {α : Type} (x : my_monad α) := monad_run.run x
    ```
    -/
class MonadRun (out : outParam <| Type u → Type v) (m : Type u → Type v) where
  run {α : Type u} : m α → out α

export MonadRun (run)

