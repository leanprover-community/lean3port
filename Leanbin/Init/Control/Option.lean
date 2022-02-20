/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Leanbin.Init.Control.Alternative
import Leanbin.Init.Control.Lift
import Leanbin.Init.Control.Except

universe u v

structure OptionTₓ (m : Type u → Type v) (α : Type u) : Type v where
  run : m (Option α)

namespace OptionTₓ

variable {m : Type u → Type v} [Monadₓ m] {α β : Type u}

@[inline]
protected def bindCont {α β : Type u} (f : α → OptionTₓ m β) : Option α → m (Option β)
  | some a => (f a).run
  | none => pure none

@[inline]
protected def bind (ma : OptionTₓ m α) (f : α → OptionTₓ m β) : OptionTₓ m β :=
  ⟨ma.run >>= OptionTₓ.bindCont f⟩

@[inline]
protected def pure (a : α) : OptionTₓ m α :=
  ⟨pure (some a)⟩

instance : Monadₓ (OptionTₓ m) where
  pure := @OptionTₓ.pure _ _
  bind := @OptionTₓ.bind _ _

protected def orelse (ma : OptionTₓ m α) (mb : OptionTₓ m α) : OptionTₓ m α :=
  ⟨do
    let some a ← ma.run | mb.run
    pure (some a)⟩

@[inline]
protected def fail : OptionTₓ m α :=
  ⟨pure none⟩

@[inline]
def ofOption : Option α → OptionTₓ m α
  | o => ⟨pure o⟩

instance : Alternativeₓ (OptionTₓ m) :=
  { OptionTₓ.monad with failure := @OptionTₓ.fail m _, orelse := @OptionTₓ.orelse m _ }

@[inline]
protected def lift (ma : m α) : OptionTₓ m α :=
  ⟨some <$> ma⟩

instance : HasMonadLift m (OptionTₓ m) :=
  ⟨@OptionTₓ.lift _ _⟩

@[inline]
protected def monadMap {m'} [Monadₓ m'] {α} (f : ∀ {α}, m α → m' α) : OptionTₓ m α → OptionTₓ m' α := fun x => ⟨f x.run⟩

instance m' [Monadₓ m'] : MonadFunctorₓ m m' (OptionTₓ m) (OptionTₓ m') :=
  ⟨fun α => OptionTₓ.monadMap⟩

protected def catch (ma : OptionTₓ m α) (handle : Unit → OptionTₓ m α) : OptionTₓ m α :=
  ⟨do
    let some a ← ma.run | (handle ()).run
    pure a⟩

instance : MonadExcept Unit (OptionTₓ m) where
  throw := fun _ _ => OptionTₓ.fail
  catch := @OptionTₓ.catch _ _

instance m out [MonadRun out m] : MonadRun (fun α => out (Option α)) (OptionTₓ m) :=
  ⟨fun α => MonadRun.run ∘ OptionTₓ.run⟩

end OptionTₓ

