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

structure OptionT (m : Type u → Type v) (α : Type u) : Type v where
  run : m (Option α)
#align option_t OptionTₓ

namespace OptionT

variable {m : Type u → Type v} [Monad m] {α β : Type u}

@[inline]
protected def bindCont {α β : Type u} (f : α → OptionT m β) : Option α → m (Option β)
  | some a => (f a).run
  | none => pure none
#align option_t.bind_cont OptionTₓ.bindCont

@[inline]
protected def bind (ma : OptionT m α) (f : α → OptionT m β) : OptionT m β :=
  ⟨ma.run >>= OptionT.bindCont f⟩
#align option_t.bind OptionTₓ.bind

@[inline]
protected def pure (a : α) : OptionT m α :=
  ⟨pure (some a)⟩
#align option_t.pure OptionTₓ.pure

instance : Monad (OptionT m) where 
  pure := @OptionT.pure _ _
  bind := @OptionT.bind _ _

protected def orelse (ma : OptionT m α) (mb : OptionT m α) : OptionT m α :=
  ⟨do
    let some a ← ma.run |
      mb.run
    pure (some a)⟩
#align option_t.orelse OptionTₓ.orelse

@[inline]
protected def fail : OptionT m α :=
  ⟨pure none⟩
#align option_t.fail OptionTₓ.fail

@[inline]
def ofOption : Option α → OptionT m α
  | o => ⟨pure o⟩
#align option_t.of_option OptionTₓ.ofOption

instance : Alternative (OptionT m) :=
  { OptionT.monad with failure := @OptionT.fail m _, orelse := @OptionT.orelse m _ }

@[inline]
protected def lift (ma : m α) : OptionT m α :=
  ⟨some <$> ma⟩
#align option_t.lift OptionTₓ.lift

instance : HasMonadLift m (OptionT m) :=
  ⟨@OptionT.lift _ _⟩

@[inline]
protected def monadMap {m'} [Monad m'] {α} (f : ∀ {α}, m α → m' α) : OptionT m α → OptionT m' α :=
  fun x => ⟨f x.run⟩
#align option_t.monad_map OptionTₓ.monadMap

instance (m') [Monad m'] : MonadFunctor m m' (OptionT m) (OptionT m') :=
  ⟨fun α => OptionT.monadMap⟩

protected def catch (ma : OptionT m α) (handle : Unit → OptionT m α) : OptionT m α :=
  ⟨do
    let some a ← ma.run |
      (handle ()).run
    pure a⟩
#align option_t.catch OptionTₓ.catch

instance : MonadExcept Unit
      (OptionT m) where 
  throw _ _ := OptionT.fail
  catch := @OptionT.catch _ _

instance (m out) [MonadRun out m] : MonadRun (fun α => out (Option α)) (OptionT m) :=
  ⟨fun α => MonadRun.run ∘ OptionT.run⟩

end OptionT

