/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The state monad transformer.
-/
prelude
import Leanbin.Init.Control.Alternative
import Leanbin.Init.Control.Lift
import Leanbin.Init.Control.Id
import Leanbin.Init.Control.Except

universe u v w

structure StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type max u v where
  run : σ → m (α × σ)

attribute [pp_using_anonymous_constructor] StateT

@[reducible]
def State (σ α : Type u) : Type u :=
  StateT σ id α

namespace StateT

section

variable {σ : Type u} {m : Type u → Type v}

variable [Monad m]

variable {α β : Type u}

@[inline]
protected def pure (a : α) : StateT σ m α :=
  ⟨fun s => pure (a, s)⟩

@[inline]
protected def bind (x : StateT σ m α) (f : α → StateT σ m β) : StateT σ m β :=
  ⟨fun s => do
    let (a, s') ← x.run s
    (f a).run s'⟩

instance : Monad (StateT σ m) where
  pure := @StateT.pure _ _ _
  bind := @StateT.bind _ _ _

protected def orelse [Alternative m] {α : Type u} (x₁ x₂ : StateT σ m α) : StateT σ m α :=
  ⟨fun s => x₁.run s <|> x₂.run s⟩

protected def failure [Alternative m] {α : Type u} : StateT σ m α :=
  ⟨fun s => failure⟩

instance [Alternative m] : Alternative (StateT σ m) where
  failure := @StateT.failure _ _ _ _
  orelse := @StateT.orelse _ _ _ _

@[inline]
protected def get : StateT σ m σ :=
  ⟨fun s => pure (s, s)⟩

@[inline]
protected def put : σ → StateT σ m PUnit := fun s' => ⟨fun s => pure (PUnit.unit, s')⟩

@[inline]
protected def modify (f : σ → σ) : StateT σ m PUnit :=
  ⟨fun s => pure (PUnit.unit, f s)⟩

@[inline]
protected def lift {α : Type u} (t : m α) : StateT σ m α :=
  ⟨fun s => do
    let a ← t
    pure (a, s)⟩

instance : HasMonadLift m (StateT σ m) :=
  ⟨@StateT.lift σ m _⟩

@[inline]
protected def monadMap {σ m m'} [Monad m] [Monad m'] {α} (f : ∀ {α}, m α → m' α) : StateT σ m α → StateT σ m' α :=
  fun x => ⟨fun st => f (x.run st)⟩

instance (σ m m') [Monad m] [Monad m'] : MonadFunctor m m' (StateT σ m) (StateT σ m') :=
  ⟨@StateT.monadMap σ m m' _ _⟩

protected def adapt {σ σ' σ'' α : Type u} {m : Type u → Type v} [Monad m] (split : σ → σ' × σ'') (join : σ' → σ'' → σ)
    (x : StateT σ' m α) : StateT σ m α :=
  ⟨fun st => do
    let (st, ctx) := split st
    let (a, st') ← x.run st
    pure (a, join st' ctx)⟩

instance (ε) [MonadExcept ε m] : MonadExcept ε (StateT σ m) where
  throw α := StateT.lift ∘ throw
  catch α x c := ⟨fun s => catch (x.run s) fun e => StateT.run (c e) s⟩

end

end StateT

/--
An implementation of [MonadState](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html).
    In contrast to the Haskell implementation, we use overlapping instances to derive instances
    automatically from `monad_lift`.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_state_lift (σ : out_param (Type u)) (n : Type u → Type u) :=
    (lift {α : Type u} : (∀ {m : Type u → Type u} [monad m], state_t σ m α) → n α)
    ```
    which better describes the intent of "we can lift a `state_t` from anywhere in the monad stack".
    However, by parametricity the types `∀ m [monad m], σ → m (α × σ)` and `σ → α × σ` should be
    equivalent because the only way to obtain an `m` is through `pure`.
    -/
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) where
  lift {α : Type u} : State σ α → m α

section

variable {σ : Type u} {m : Type u → Type v}

-- NOTE: The ordering of the following two instances determines that the top-most `state_t` monad layer
-- will be picked first
instance (priority := 100) monadStateTrans {n : Type u → Type w} [MonadState σ m] [HasMonadLift m n] : MonadState σ n :=
  ⟨fun α x => monadLift (MonadState.lift x : m α)⟩

instance [Monad m] : MonadState σ (StateT σ m) :=
  ⟨fun α x => ⟨fun s => pure (x.run s)⟩⟩

variable [Monad m] [MonadState σ m]

/-- Obtain the top-most state of a monad stack. -/
@[inline]
def get : m σ :=
  MonadState.lift StateT.get

/-- Set the top-most state of a monad stack. -/
@[inline]
def put (st : σ) : m PUnit :=
  MonadState.lift (StateT.put st)

/- warning: modify -> modify is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u}} {m : Type.{u} -> Type.{v}} [_inst_1 : Monad.{u v} m] [_inst_2 : MonadState.{u v} σ m], (σ -> σ) -> (m PUnit.{succ u})
but is expected to have type
  forall {σ : Type.{u}} {m : Type.{u} -> Type.{v}} [inst._@.Init.Prelude._hyg.11916 : MonadState.{u v} σ m], (σ -> σ) -> (m PUnit.{succ u})
Case conversion may be inaccurate. Consider using '#align modify modifyₓ'. -/
/-- Map the top-most state of a monad stack.

    Note: `modify f` may be preferable to `f <$> get >>= put` because the latter
    does not use the state linearly (without sufficient inlining). -/
@[inline]
def modify (f : σ → σ) : m PUnit :=
  MonadState.lift (StateT.modify f)

end

/-- Adapt a monad stack, changing the type of its top-most state.

    This class is comparable to [Control.Lens.Zoom](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Zoom), but does not use lenses (yet?), and is derived automatically for any transformer implementing `monad_functor`.

    For zooming into a part of the state, the `split` function should split σ into the part σ' and the "context" σ'' so that the potentially modified σ' and the context can be rejoined by `join` in the end.
    In the simplest case, the context can be chosen as the full outer state (ie. `σ'' = σ`), which makes `split` and `join` simpler to define. However, note that the state will not be used linearly in this case.

    Example:
    ```
    def zoom_fst {α σ σ' : Type} : state σ α → state (σ × σ') α :=
    adapt_state id prod.mk
    ```

    The function can also zoom out into a "larger" state, where the new parts are supplied by `split` and discarded by `join` in the end. The state is therefore not used linearly anymore but merely affinely, which is not a practically relevant distinction in Lean.

    Example:
    ```
    def with_snd {α σ σ' : Type} (snd : σ') : state (σ × σ') α → state σ α :=
    adapt_state (λ st, ((st, snd), ())) (λ ⟨st,snd⟩ _, st)
    ```

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_state_functor (σ σ' : out_param (Type u)) (n n' : Type u → Type u) :=
    (map {α : Type u} : (∀ {m : Type u → Type u} [monad m], state_t σ m α → state_t σ' m α) → n α → n' α)
    ```
    which better describes the intent of "we can map a `state_t` anywhere in the monad stack".
    If we look at the unfolded type of the first argument `∀ m [monad m], (σ → m (α × σ)) → σ' → m (α × σ')`, we see that it has the lens type `∀ f [functor f], (α → f α) → β → f β` with `f` specialized to `λ σ, m (α × σ)` (exercise: show that this is a lawful functor). We can build all lenses we are insterested in from the functions `split` and `join` as
    ```
    λ f _ st, let (st, ctx) := split st in
              (λ st', join st' ctx) <$> f st
    ```
    -/
class MonadStateAdapter (σ σ' : outParam (Type u)) (m m' : Type u → Type v) where
  adaptState {σ'' α : Type u} (split : σ' → σ × σ'') (join : σ → σ'' → σ') : m α → m' α

export MonadStateAdapter (adaptState)

section

variable {σ σ' : Type u} {m m' : Type u → Type v}

instance (priority := 100) monadStateAdapterTrans {n n' : Type u → Type v} [MonadStateAdapter σ σ' m m']
    [MonadFunctor m m' n n'] : MonadStateAdapter σ σ' n n' :=
  ⟨fun σ'' α split join => monadMap fun α => (adaptState split join : m α → m' α)⟩

instance [Monad m] : MonadStateAdapter σ σ' (StateT σ m) (StateT σ' m) :=
  ⟨fun σ'' α => StateT.adapt⟩

end

instance (σ m out) [MonadRun out m] : MonadRun (fun α => σ → out (α × σ)) (StateT σ m) :=
  ⟨fun α x => run ∘ fun σ => x.run σ⟩

