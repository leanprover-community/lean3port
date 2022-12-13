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

/-- A function for lifting a computation from an inner monad to an outer monad.
    Like [MonadTrans](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Class.html),
    but `n` does not have to be a monad transformer.
    Alternatively, an implementation of [MonadLayer](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLayer) without `layerInvmap` (so far). -/
class HasMonadLift (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : ∀ {α}, m α → n α
#align has_monad_lift HasMonadLift

/-- The reflexive-transitive closure of `has_monad_lift`.
    `monad_lift` is used to transitively lift monadic computations such as `state_t.get` or `state_t.put s`.
    Corresponds to [MonadLift](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLift). -/
class HasMonadLiftT (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : ∀ {α}, m α → n α
#align has_monad_lift_t HasMonadLiftT

export HasMonadLiftT (monadLift)

/-- A coercion that may reduce the need for explicit lifting.
    Because of [limitations of the current coercion resolution](https://github.com/leanprover/lean/issues/1402), this definition is not marked as a global instance and should be marked locally instead. -/
@[reducible]
def hasMonadLiftToHasCoe {m n} [HasMonadLiftT m n] {α} : Coe (m α) (n α) :=
  ⟨monadLift⟩
#align has_monad_lift_to_has_coe hasMonadLiftToHasCoe

instance (priority := 100) hasMonadLiftTTrans (m n o) [HasMonadLiftT m n] [HasMonadLift n o] :
    HasMonadLiftT m o :=
  ⟨fun α ma => HasMonadLift.monadLift (monadLift ma : n α)⟩
#align has_monad_lift_t_trans hasMonadLiftTTrans

instance hasMonadLiftTRefl (m) : HasMonadLiftT m m :=
  ⟨fun α => id⟩
#align has_monad_lift_t_refl hasMonadLiftTRefl

@[simp]
theorem monad_lift_refl {m : Type u → Type v} {α} : (monadLift : m α → m α) = id :=
  rfl
#align monad_lift_refl monad_lift_refl

/- warning: monad_functor -> MonadFunctor is a dubious translation:
lean 3 declaration is
  (Type.{u1} -> Type.{u2}) -> (Type.{u1} -> Type.{u2}) -> (Type.{u1} -> Type.{u3}) -> (Type.{u1} -> Type.{u3}) -> Sort.{max (succ (succ u1)) (succ u2) (succ u3)}
but is expected to have type
  (Type.{u1} -> Type.{u2}) -> (Type.{u1} -> Type.{u3}) -> Sort.{max (max (succ (succ u1)) (succ u2)) (succ u3)}
Case conversion may be inaccurate. Consider using '#align monad_functor MonadFunctorₓ'. -/
/-- A functor in the category of monads. Can be used to lift monad-transforming functions.
    Based on pipes' [MFunctor](https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html),
    but not restricted to monad transformers.
    Alternatively, an implementation of [MonadTransFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadTransFunctor). -/
class MonadFunctor (m m' : Type u → Type v) (n n' : Type u → Type w) where
  monadMap {α : Type u} : (∀ {α}, m α → m' α) → n α → n' α
#align monad_functor MonadFunctor

/- warning: monad_functor_t -> MonadFunctorT is a dubious translation:
lean 3 declaration is
  (Type.{u1} -> Type.{u2}) -> (Type.{u1} -> Type.{u2}) -> (Type.{u1} -> Type.{u3}) -> (Type.{u1} -> Type.{u3}) -> Sort.{max (succ (succ u1)) (succ u2) (succ u3)}
but is expected to have type
  (Type.{u1} -> Type.{u2}) -> (Type.{u1} -> Type.{u3}) -> Sort.{max (max (succ (succ u1)) (succ u2)) (succ u3)}
Case conversion may be inaccurate. Consider using '#align monad_functor_t MonadFunctorTₓ'. -/
/-- The reflexive-transitive closure of `monad_functor`.
    `monad_map` is used to transitively lift monad morphisms such as `state_t.zoom`.
    A generalization of [MonadLiftFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadLiftFunctor), which can only lift endomorphisms (i.e. m = m', n = n'). -/
class MonadFunctorT (m m' : Type u → Type v) (n n' : Type u → Type w) where
  monadMap {α : Type u} : (∀ {α}, m α → m' α) → n α → n' α
#align monad_functor_t MonadFunctorT

export MonadFunctorT (monadMap)

instance (priority := 100) monadFunctorTTrans (m m' n n' o o') [MonadFunctorT m m' n n']
    [MonadFunctor n n' o o'] : MonadFunctorT m m' o o' :=
  ⟨fun α f => MonadFunctor.monadMap fun α => (monadMap @f : n α → n' α)⟩
#align monad_functor_t_trans monadFunctorTTrans

instance monadFunctorTRefl (m m') : MonadFunctorT m m' m m' :=
  ⟨fun α f => f⟩
#align monad_functor_t_refl monadFunctorTRefl

@[simp]
theorem monad_map_refl {m m' : Type u → Type v} (f : ∀ {α}, m α → m' α) {α} :
    (monadMap @f : m α → m' α) = f :=
  rfl
#align monad_map_refl monad_map_refl

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
#align monad_run MonadRun

export MonadRun (run)

