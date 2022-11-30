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
structure ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type max u v where
  run : ρ → m α
#align reader_t ReaderTₓ

@[reducible]
def Reader (ρ : Type u) :=
  ReaderT ρ id
#align reader Reader

attribute [pp_using_anonymous_constructor] ReaderT

namespace ReaderT

section

variable {ρ : Type u}

variable {m : Type u → Type v}

variable [Monad m]

variable {α β : Type u}

@[inline]
protected def read : ReaderT ρ m ρ :=
  ⟨pure⟩
#align reader_t.read ReaderTₓ.read

@[inline]
protected def pure (a : α) : ReaderT ρ m α :=
  ⟨fun r => pure a⟩
#align reader_t.pure ReaderTₓ.pure

@[inline]
protected def bind (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) : ReaderT ρ m β :=
  ⟨fun r => do
    let a ← x.run r
    (f a).run r⟩
#align reader_t.bind ReaderTₓ.bind

instance : Monad (ReaderT ρ m) where 
  pure := @ReaderT.pure _ _ _
  bind := @ReaderT.bind _ _ _

@[inline]
protected def lift (a : m α) : ReaderT ρ m α :=
  ⟨fun r => a⟩
#align reader_t.lift ReaderTₓ.lift

instance (m) [Monad m] : HasMonadLift m (ReaderT ρ m) :=
  ⟨@ReaderT.lift ρ m _⟩

@[inline]
protected def monadMap {ρ m m'} [Monad m] [Monad m'] {α} (f : ∀ {α}, m α → m' α) :
    ReaderT ρ m α → ReaderT ρ m' α := fun x => ⟨fun r => f (x.run r)⟩
#align reader_t.monad_map ReaderTₓ.monadMap

instance (ρ m m') [Monad m] [Monad m'] : MonadFunctor m m' (ReaderT ρ m) (ReaderT ρ m') :=
  ⟨@ReaderT.monadMap ρ m m' _ _⟩

@[inline]
protected def adapt {ρ' : Type u} [Monad m] {α : Type u} (f : ρ' → ρ) :
    ReaderT ρ m α → ReaderT ρ' m α := fun x => ⟨fun r => x.run (f r)⟩
#align reader_t.adapt ReaderTₓ.adapt

protected def orelse [Alternative m] {α : Type u} (x₁ x₂ : ReaderT ρ m α) : ReaderT ρ m α :=
  ⟨fun s => x₁.run s <|> x₂.run s⟩
#align reader_t.orelse ReaderTₓ.orelse

protected def failure [Alternative m] {α : Type u} : ReaderT ρ m α :=
  ⟨fun s => failure⟩
#align reader_t.failure ReaderTₓ.failure

instance [Alternative m] :
    Alternative (ReaderT ρ
        m) where 
  failure := @ReaderT.failure _ _ _ _
  orelse := @ReaderT.orelse _ _ _ _

instance (ε) [Monad m] [MonadExcept ε m] :
    MonadExcept ε (ReaderT ρ
        m) where 
  throw α := ReaderT.lift ∘ throw
  catch α x c := ⟨fun r => catch (x.run r) fun e => (c e).run r⟩

end

end ReaderT

#print MonadReader /-
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
#align monad_reader MonadReader
-/

export MonadReader (read)

instance (priority := 100) monadReaderTrans {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w}
    [MonadReader ρ m] [HasMonadLift m n] : MonadReader ρ n :=
  ⟨monadLift (MonadReader.read : m ρ)⟩
#align monad_reader_trans monadReaderTrans

instance {ρ : Type u} {m : Type u → Type v} [Monad m] : MonadReader ρ (ReaderT ρ m) :=
  ⟨ReaderT.read⟩

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
#align monad_reader_adapter MonadReaderAdapter

export MonadReaderAdapter (adaptReader)

section

variable {ρ ρ' : Type u} {m m' : Type u → Type v}

instance (priority := 100) monadReaderAdapterTrans {n n' : Type u → Type v}
    [MonadReaderAdapter ρ ρ' m m'] [MonadFunctor m m' n n'] : MonadReaderAdapter ρ ρ' n n' :=
  ⟨fun α f => monadMap fun α => (adaptReader f : m α → m' α)⟩
#align monad_reader_adapter_trans monadReaderAdapterTrans

instance [Monad m] : MonadReaderAdapter ρ ρ' (ReaderT ρ m) (ReaderT ρ' m) :=
  ⟨fun α => ReaderT.adapt⟩

end

instance (ρ : Type u) (m out) [MonadRun out m] : MonadRun (fun α => ρ → out α) (ReaderT ρ m) :=
  ⟨fun α x => run ∘ x.run⟩

