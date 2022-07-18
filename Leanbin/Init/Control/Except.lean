/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch, Sebastian Ullrich

The except monad transformer.
-/
prelude
import Leanbin.Init.Control.Alternative
import Leanbin.Init.Control.Lift

universe u v w

inductive Except (ε : Type u) (α : Type v)
  | error : ε → Except
  | ok : α → Except

namespace Except

section

parameter {ε : Type u}

protected def return {α : Type v} (a : α) : Except ε α :=
  Except.ok a

protected def mapₓ {α β : Type v} (f : α → β) : Except ε α → Except ε β
  | Except.error err => Except.error err
  | Except.ok v => Except.ok <| f v

protected def mapErrorₓ {ε' : Type u} {α : Type v} (f : ε → ε') : Except ε α → Except ε' α
  | Except.error err => Except.error <| f err
  | Except.ok v => Except.ok v

protected def bindₓ {α β : Type v} (ma : Except ε α) (f : α → Except ε β) : Except ε β :=
  match ma with
  | Except.error err => Except.error err
  | Except.ok v => f v

protected def toBool {α : Type v} : Except ε α → Bool
  | Except.ok _ => true
  | Except.error _ => false

protected def toOption {α : Type v} : Except ε α → Option α
  | Except.ok a => some a
  | Except.error _ => none

instance : Monadₓ (Except ε) where
  pure := @return
  bind := @bind

end

end Except

structure ExceptTₓ (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v where
  run : m (Except ε α)

attribute [pp_using_anonymous_constructor] ExceptTₓ

namespace ExceptTₓ

section

parameter {ε : Type u}{m : Type u → Type v}[Monadₓ m]

@[inline]
protected def return {α : Type u} (a : α) : ExceptTₓ ε m α :=
  ⟨pure <| Except.ok a⟩

@[inline]
protected def bindCont {α β : Type u} (f : α → ExceptTₓ ε m β) : Except ε α → m (Except ε β)
  | Except.ok a => (f a).run
  | Except.error e => pure (Except.error e)

@[inline]
protected def bind {α β : Type u} (ma : ExceptTₓ ε m α) (f : α → ExceptTₓ ε m β) : ExceptTₓ ε m β :=
  ⟨ma.run >>= bind_cont f⟩

@[inline]
protected def lift {α : Type u} (t : m α) : ExceptTₓ ε m α :=
  ⟨Except.ok <$> t⟩

instance : HasMonadLift m (ExceptTₓ ε m) :=
  ⟨@ExceptTₓ.lift⟩

protected def catch {α : Type u} (ma : ExceptTₓ ε m α) (handle : ε → ExceptTₓ ε m α) : ExceptTₓ ε m α :=
  ⟨ma.run >>= fun res =>
      match res with
      | Except.ok a => pure (Except.ok a)
      | Except.error e => (handle e).run⟩

@[inline]
protected def monadMap {m'} [Monadₓ m'] {α} (f : ∀ {α}, m α → m' α) : ExceptTₓ ε m α → ExceptTₓ ε m' α := fun x =>
  ⟨f x.run⟩

instance (m') [Monadₓ m'] : MonadFunctorₓ m m' (ExceptTₓ ε m) (ExceptTₓ ε m') :=
  ⟨@monad_map m' _⟩

instance : Monadₓ (ExceptTₓ ε m) where
  pure := @return
  bind := @bind

protected def adapt {ε' α : Type u} (f : ε → ε') : ExceptTₓ ε m α → ExceptTₓ ε' m α := fun x =>
  ⟨Except.mapErrorₓ f <$> x.run⟩

end

end ExceptTₓ

/--
An implementation of [MonadError](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Except.html#t:MonadError) -/
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
  throw {α : Type v} : ε → m α
  catch {α : Type v} : m α → (ε → m α) → m α

namespace MonadExcept

variable {ε : Type u} {m : Type v → Type w}

protected def orelse [MonadExcept ε m] {α : Type v} (t₁ t₂ : m α) : m α :=
  (catch t₁) fun _ => t₂

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
unsafe def orelse' [MonadExcept ε m] {α : Type v} (t₁ t₂ : m α) (use_first_ex := true) : m α :=
  (catch t₁) fun e₁ => (catch t₂) fun e₂ => throw (if use_first_ex then e₁ else e₂)

end MonadExcept

export MonadExcept (throw catch)

instance (m ε) [Monadₓ m] : MonadExcept ε (ExceptTₓ ε m) where
  throw := fun α => ExceptTₓ.mk ∘ pure ∘ Except.error
  catch := @ExceptTₓ.catch ε _ _

/-- Adapt a monad stack, changing its top-most error type.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_except_functor (ε ε' : out_param (Type u)) (n n' : Type u → Type u) :=
    (map {α : Type u} : (∀ {m : Type u → Type u} [monad m], except_t ε m α → except_t ε' m α) → n α → n' α)
    ```
    -/
class MonadExceptAdapter (ε ε' : outParam (Type u)) (m m' : Type u → Type v) where
  adaptExcept {α : Type u} : (ε → ε') → m α → m' α

export MonadExceptAdapter (adaptExcept)

section

variable {ε ε' : Type u} {m m' : Type u → Type v}

instance (priority := 100) monadExceptAdapterTrans {n n' : Type u → Type v} [MonadExceptAdapter ε ε' m m']
    [MonadFunctorₓ m m' n n'] : MonadExceptAdapter ε ε' n n' :=
  ⟨fun α f => monadMap fun α => (adaptExcept f : m α → m' α)⟩

instance [Monadₓ m] : MonadExceptAdapter ε ε' (ExceptTₓ ε m) (ExceptTₓ ε' m) :=
  ⟨fun α => ExceptTₓ.adapt⟩

end

instance (ε m out) [MonadRun out m] : MonadRun (fun α => out (Except ε α)) (ExceptTₓ ε m) :=
  ⟨fun α => run ∘ ExceptTₓ.run⟩

