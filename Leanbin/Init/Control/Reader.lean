/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The reader monad transformer for passing immutable state.
-/
prelude
import Leanbin.Init.Control.Lift
import Leanbin.Init.Control.Id
import Leanbin.Init.Control.Alternative
import Leanbin.Init.Control.Except

universe u v w

/--
An implementation of [ReaderT](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Reader.html#t:ReaderT) -/
structure ReaderTₓ (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type max u v where
  run : ρ → m α

@[reducible]
def Readerₓ (ρ : Type u) :=
  ReaderTₓ ρ id

attribute [pp_using_anonymous_constructor] ReaderTₓ

namespace ReaderTₓ

section

variable {ρ : Type u}

variable {m : Type u → Type v}

variable [Monadₓ m]

variable {α β : Type u}

@[inline]
protected def read : ReaderTₓ ρ m ρ :=
  ⟨pure⟩

@[inline]
protected def pure (a : α) : ReaderTₓ ρ m α :=
  ⟨fun r => pure a⟩

@[inline]
protected def bind (x : ReaderTₓ ρ m α) (f : α → ReaderTₓ ρ m β) : ReaderTₓ ρ m β :=
  ⟨fun r => do
    let a ← x.run r
    (f a).run r⟩

instance : Monadₓ (ReaderTₓ ρ m) where
  pure := @ReaderTₓ.pure _ _ _
  bind := @ReaderTₓ.bind _ _ _

@[inline]
protected def lift (a : m α) : ReaderTₓ ρ m α :=
  ⟨fun r => a⟩

instance m [Monadₓ m] : HasMonadLift m (ReaderTₓ ρ m) :=
  ⟨@ReaderTₓ.lift ρ m _⟩

@[inline]
protected def monadMap {ρ m m'} [Monadₓ m] [Monadₓ m'] {α} (f : ∀ {α}, m α → m' α) : ReaderTₓ ρ m α → ReaderTₓ ρ m' α :=
  fun x => ⟨fun r => f (x.run r)⟩

instance ρ m m' [Monadₓ m] [Monadₓ m'] : MonadFunctorₓ m m' (ReaderTₓ ρ m) (ReaderTₓ ρ m') :=
  ⟨@ReaderTₓ.monadMap ρ m m' _ _⟩

@[inline]
protected def adapt {ρ' : Type u} [Monadₓ m] {α : Type u} (f : ρ' → ρ) : ReaderTₓ ρ m α → ReaderTₓ ρ' m α := fun x =>
  ⟨fun r => x.run (f r)⟩

protected def orelse [Alternativeₓ m] {α : Type u} (x₁ x₂ : ReaderTₓ ρ m α) : ReaderTₓ ρ m α :=
  ⟨fun s => x₁.run s <|> x₂.run s⟩

protected def failure [Alternativeₓ m] {α : Type u} : ReaderTₓ ρ m α :=
  ⟨fun s => failure⟩

instance [Alternativeₓ m] : Alternativeₓ (ReaderTₓ ρ m) where
  failure := @ReaderTₓ.failure _ _ _ _
  orelse := @ReaderTₓ.orelse _ _ _ _

instance ε [Monadₓ m] [MonadExcept ε m] : MonadExcept ε (ReaderTₓ ρ m) where
  throw := fun α => ReaderTₓ.lift ∘ throw
  catch := fun α x c => ⟨fun r => catch (x.run r) fun e => (c e).run r⟩

end

end ReaderTₓ

/--
An implementation of [MonadReader](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
    It does not contain `local` because this function cannot be lifted using `monad_lift`.
    Instead, the `monad_reader_adapter` class provides the more general `adapt_reader` function.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_reader (ρ : out_param (Type u)) (n : Type u → Type u) :=
    (lift {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α) → n α)
    ```
    -/
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  read : m ρ

export MonadReader (read)

instance (priority := 100) monadReaderTrans {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w} [MonadReader ρ m]
    [HasMonadLift m n] : MonadReader ρ n :=
  ⟨monadLift (MonadReader.read : m ρ)⟩

instance {ρ : Type u} {m : Type u → Type v} [Monadₓ m] : MonadReader ρ (ReaderTₓ ρ m) :=
  ⟨ReaderTₓ.read⟩

/-- Adapt a monad stack, changing the type of its top-most environment.

    This class is comparable to [Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify), but does not use lenses (why would it), and is derived automatically for any transformer implementing `monad_functor`.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_reader_functor (ρ ρ' : out_param (Type u)) (n n' : Type u → Type u) :=
    (map {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α → reader_t ρ' m α) → n α → n' α)
    ```
    -/
class MonadReaderAdapter (ρ ρ' : outParam (Type u)) (m m' : Type u → Type v) where
  adaptReader {α : Type u} : (ρ' → ρ) → m α → m' α

export MonadReaderAdapter (adaptReader)

section

variable {ρ ρ' : Type u} {m m' : Type u → Type v}

instance (priority := 100) monadReaderAdapterTrans {n n' : Type u → Type v} [MonadReaderAdapter ρ ρ' m m']
    [MonadFunctorₓ m m' n n'] : MonadReaderAdapter ρ ρ' n n' :=
  ⟨fun α f => monadMap fun α => (adaptReader f : m α → m' α)⟩

instance [Monadₓ m] : MonadReaderAdapter ρ ρ' (ReaderTₓ ρ m) (ReaderTₓ ρ' m) :=
  ⟨fun α => ReaderTₓ.adapt⟩

end

instance (ρ : Type u) m out [MonadRun out m] : MonadRun (fun α => ρ → out α) (ReaderTₓ ρ m) :=
  ⟨fun α x => run ∘ x.run⟩

