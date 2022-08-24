/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Leanbin.Init.Control.Monad
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Control.State
import Leanbin.Init.Control.Except
import Leanbin.Init.Control.Reader
import Leanbin.Init.Control.Option

universe u v

open Function

open Tactic

unsafe def control_laws_tac :=
  (whnf_target >> intros) >> to_expr (pquote.1 rfl) >>= exact

class IsLawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  map_const_eq : ∀ {α β : Type u}, ((· <$ ·) : α → f β → f α) = (· <$> ·) ∘ const β := by
    run_tac
      control_laws_tac
  -- `functor` is indeed a categorical functor
  id_map : ∀ {α : Type u} (x : f α), id <$> x = x
  comp_map : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x

export IsLawfulFunctor (map_const_eq id_map comp_map)

attribute [simp] id_map

-- `comp_map` does not make a good simp lemma
class IsLawfulApplicative (f : Type u → Type v) [Applicativeₓ f] extends IsLawfulFunctor f : Prop where
  seq_left_eq : ∀ {α β : Type u} (a : f α) (b : f β), a <* b = const β <$> a <*> b := by
    run_tac
      control_laws_tac
  seq_right_eq : ∀ {α β : Type u} (a : f α) (b : f β), a *> b = const α id <$> a <*> b := by
    run_tac
      control_laws_tac
  -- applicative laws
  pure_seq_eq_map : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x
  map_pure : ∀ {α β : Type u} (g : α → β) (x : α), g <$> (pure x : f α) = pure (g x)
  seq_pure : ∀ {α β : Type u} (g : f (α → β)) (x : α), g <*> pure x = (fun g : α → β => g x) <$> g
  seq_assoc :
    ∀ {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)), h <*> (g <*> x) = @comp α β γ <$> h <*> g <*> x
  -- default functor law
  comp_map := by
    intros <;> simp [(pure_seq_eq_map _ _).symm, seq_assoc, map_pure, seq_pure]

export IsLawfulApplicative (seq_left_eq seq_right_eq pure_seq_eq_map map_pure seq_pure seq_assoc)

attribute [simp] map_pure seq_pure

-- applicative "law" derivable from other laws
@[simp]
theorem pure_id_seqₓ {α : Type u} {f : Type u → Type v} [Applicativeₓ f] [IsLawfulApplicative f] (x : f α) :
    pure id <*> x = x := by
  simp [pure_seq_eq_map]

class IsLawfulMonad (m : Type u → Type v) [Monadₓ m] extends IsLawfulApplicative m : Prop where
  bind_pure_comp_eq_map : ∀ {α β : Type u} (f : α → β) (x : m α), x >>= pure ∘ f = f <$> x := by
    run_tac
      control_laws_tac
  bind_map_eq_seq : ∀ {α β : Type u} (f : m (α → β)) (x : m α), f >>= (· <$> x) = f <*> x := by
    run_tac
      control_laws_tac
  -- monad laws
  pure_bind : ∀ {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
  bind_assoc : ∀ {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ), x >>= f >>= g = x >>= fun x => f x >>= g
  pure_seq_eq_map := by
    intros <;> rw [← bind_map_eq_seq] <;> simp [pure_bind]
  map_pure := by
    intros <;> rw [← bind_pure_comp_eq_map] <;> simp [pure_bind]
  seq_pure := by
    intros <;> rw [← bind_map_eq_seq] <;> simp [map_pure, bind_pure_comp_eq_map]
  seq_assoc := by
    intros <;> simp [(bind_pure_comp_eq_map _ _).symm, (bind_map_eq_seq _ _).symm, bind_assoc, pure_bind]

export IsLawfulMonad (bind_pure_comp_eq_map bind_map_eq_seq pure_bind bind_assoc)

attribute [simp] pure_bind

-- monad "law" derivable from other laws
@[simp]
theorem bind_pureₓ {α : Type u} {m : Type u → Type v} [Monadₓ m] [IsLawfulMonad m] (x : m α) : x >>= pure = x :=
  show x >>= pure ∘ id = x by
    rw [bind_pure_comp_eq_map] <;> simp [id_map]

theorem bind_ext_congr {α β} {m : Type u → Type v} [Bind m] {x : m α} {f g : α → m β} :
    (∀ a, f a = g a) → x >>= f = x >>= g := fun h => by
  simp [show f = g from funext h]

theorem map_ext_congr {α β} {m : Type u → Type v} [Functor m] {x : m α} {f g : α → β} :
    (∀ a, f a = g a) → (f <$> x : m β) = g <$> x := fun h => by
  simp [show f = g from funext h]

-- instances of previously defined monads
namespace id

variable {α β : Type}

@[simp]
theorem map_eq (x : id α) (f : α → β) : f <$> x = f x :=
  rfl

@[simp]
theorem bind_eq (x : id α) (f : α → id β) : x >>= f = f x :=
  rfl

@[simp]
theorem pure_eq (a : α) : (pure a : id α) = a :=
  rfl

end id

instance : IsLawfulMonad id := by
  refine' { .. } <;> intros <;> rfl

namespace StateTₓ

section

variable {σ : Type u}

variable {m : Type u → Type v}

variable {α β : Type u}

variable (x : StateTₓ σ m α) (st : σ)

theorem ext {x x' : StateTₓ σ m α} (h : ∀ st, x.run st = x'.run st) : x = x' := by
  cases x <;> cases x' <;> simp [show x = x' from funext h]

variable [Monadₓ m]

@[simp]
theorem run_pure (a) : (pure a : StateTₓ σ m α).run st = pure (a, st) :=
  rfl

@[simp]
theorem run_bind (f : α → StateTₓ σ m β) : (x >>= f).run st = x.run st >>= fun p => (f p.1).run p.2 := by
  apply bind_ext_congr <;> intro a <;> cases a <;> simp [StateTₓ.bind, StateTₓ.run]

@[simp]
theorem run_map (f : α → β) [IsLawfulMonad m] :
    (f <$> x).run st = (fun p : α × σ => (f (Prod.fst p), Prod.snd p)) <$> x.run st := by
  rw [← bind_pure_comp_eq_map _ (x.run st)]
  change (x >>= pure ∘ f).run st = _
  simp

@[simp]
theorem run_monad_lift {n} [HasMonadLiftT n m] (x : n α) :
    (monadLift x : StateTₓ σ m α).run st = do
      let a ← (monadLift x : m α)
      pure (a, st) :=
  rfl

@[simp]
theorem run_monad_map {m' n n'} [Monadₓ m'] [MonadFunctorTₓ n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : StateTₓ σ m' α).run st = monadMap (@f) (x.run st) :=
  rfl

@[simp]
theorem run_adapt {σ' σ''} (st : σ) (split : σ → σ' × σ'') (join : σ' → σ'' → σ) (x : StateTₓ σ' m α) :
    (StateTₓ.adapt split join x : StateTₓ σ m α).run st = do
      let (st, ctx) := split st
      let (a, st') ← x.run st
      pure (a, join st' ctx) :=
  by
  delta' StateTₓ.adapt <;> rfl

@[simp]
theorem run_get : (StateTₓ.get : StateTₓ σ m σ).run st = pure (st, st) :=
  rfl

@[simp]
theorem run_put (st') : (StateTₓ.put st' : StateTₓ σ m _).run st = pure (PUnit.unit, st') :=
  rfl

end

end StateTₓ

instance (m : Type u → Type v) [Monadₓ m] [IsLawfulMonad m] (σ : Type u) : IsLawfulMonad (StateTₓ σ m) where
  id_map := by
    intros <;> apply StateTₓ.ext <;> intro <;> simp <;> erw [id_map]
  pure_bind := by
    intros
    apply StateTₓ.ext
    simp
  bind_assoc := by
    intros
    apply StateTₓ.ext
    simp [bind_assoc]

namespace ExceptTₓ

variable {α β ε : Type u} {m : Type u → Type v} (x : ExceptTₓ ε m α)

theorem ext {x x' : ExceptTₓ ε m α} (h : x.run = x'.run) : x = x' := by
  cases x <;> cases x' <;> simp_all

variable [Monadₓ m]

@[simp]
theorem run_pure (a) : (pure a : ExceptTₓ ε m α).run = pure (@Except.ok ε α a) :=
  rfl

@[simp]
theorem run_bind (f : α → ExceptTₓ ε m β) : (x >>= f).run = x.run >>= ExceptTₓ.bindCont f :=
  rfl

@[simp]
theorem run_map (f : α → β) [IsLawfulMonad m] : (f <$> x).run = Except.mapₓ f <$> x.run := by
  rw [← bind_pure_comp_eq_map _ x.run]
  change x.run >>= ExceptTₓ.bindCont (pure ∘ f) = _
  apply bind_ext_congr
  intro a <;> cases a <;> simp [ExceptTₓ.bindCont, Except.mapₓ]

@[simp]
theorem run_monad_lift {n} [HasMonadLiftT n m] (x : n α) :
    (monadLift x : ExceptTₓ ε m α).run = Except.ok <$> (monadLift x : m α) :=
  rfl

@[simp]
theorem run_monad_map {m' n n'} [Monadₓ m'] [MonadFunctorTₓ n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : ExceptTₓ ε m' α).run = monadMap (@f) x.run :=
  rfl

end ExceptTₓ

instance (m : Type u → Type v) [Monadₓ m] [IsLawfulMonad m] (ε : Type u) : IsLawfulMonad (ExceptTₓ ε m) where
  id_map := by
    intros
    apply ExceptTₓ.ext
    simp only [ExceptTₓ.run_map]
    rw [map_ext_congr, id_map]
    intro a
    cases a <;> rfl
  bind_pure_comp_eq_map := by
    intros
    apply ExceptTₓ.ext
    simp only [ExceptTₓ.run_map, ExceptTₓ.run_bind]
    rw [bind_ext_congr, bind_pure_comp_eq_map]
    intro a
    cases a <;> rfl
  bind_assoc := by
    intros
    apply ExceptTₓ.ext
    simp only [ExceptTₓ.run_bind, bind_assoc]
    rw [bind_ext_congr]
    intro a
    cases a <;> simp [ExceptTₓ.bindCont]
  pure_bind := by
    intros <;> apply ExceptTₓ.ext <;> simp [ExceptTₓ.bindCont]

namespace ReaderTₓ

section

variable {ρ : Type u}

variable {m : Type u → Type v}

variable {α β : Type u}

variable (x : ReaderTₓ ρ m α) (r : ρ)

theorem ext {x x' : ReaderTₓ ρ m α} (h : ∀ r, x.run r = x'.run r) : x = x' := by
  cases x <;> cases x' <;> simp [show x = x' from funext h]

variable [Monadₓ m]

@[simp]
theorem run_pure (a) : (pure a : ReaderTₓ ρ m α).run r = pure a :=
  rfl

@[simp]
theorem run_bind (f : α → ReaderTₓ ρ m β) : (x >>= f).run r = x.run r >>= fun a => (f a).run r :=
  rfl

@[simp]
theorem run_map (f : α → β) [IsLawfulMonad m] : (f <$> x).run r = f <$> x.run r := by
  rw [← bind_pure_comp_eq_map _ (x.run r)] <;> rfl

@[simp]
theorem run_monad_lift {n} [HasMonadLiftT n m] (x : n α) : (monadLift x : ReaderTₓ ρ m α).run r = (monadLift x : m α) :=
  rfl

@[simp]
theorem run_monad_map {m' n n'} [Monadₓ m'] [MonadFunctorTₓ n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : ReaderTₓ ρ m' α).run r = monadMap (@f) (x.run r) :=
  rfl

@[simp]
theorem run_read : (ReaderTₓ.read : ReaderTₓ ρ m ρ).run r = pure r :=
  rfl

end

end ReaderTₓ

instance (ρ : Type u) (m : Type u → Type v) [Monadₓ m] [IsLawfulMonad m] : IsLawfulMonad (ReaderTₓ ρ m) where
  id_map := by
    intros <;> apply ReaderTₓ.ext <;> intro <;> simp
  pure_bind := by
    intros <;> apply ReaderTₓ.ext <;> intro <;> simp
  bind_assoc := by
    intros <;> apply ReaderTₓ.ext <;> intro <;> simp [bind_assoc]

namespace OptionTₓ

variable {α β : Type u} {m : Type u → Type v} (x : OptionTₓ m α)

theorem ext {x x' : OptionTₓ m α} (h : x.run = x'.run) : x = x' := by
  cases x <;> cases x' <;> simp_all

variable [Monadₓ m]

@[simp]
theorem run_pure (a) : (pure a : OptionTₓ m α).run = pure (some a) :=
  rfl

@[simp]
theorem run_bind (f : α → OptionTₓ m β) : (x >>= f).run = x.run >>= OptionTₓ.bindCont f :=
  rfl

@[simp]
theorem run_map (f : α → β) [IsLawfulMonad m] : (f <$> x).run = Option.map f <$> x.run := by
  rw [← bind_pure_comp_eq_map _ x.run]
  change x.run >>= OptionTₓ.bindCont (pure ∘ f) = _
  apply bind_ext_congr
  intro a <;> cases a <;> simp [OptionTₓ.bindCont, Option.map, Option.bind]

@[simp]
theorem run_monad_lift {n} [HasMonadLiftT n m] (x : n α) :
    (monadLift x : OptionTₓ m α).run = some <$> (monadLift x : m α) :=
  rfl

@[simp]
theorem run_monad_map {m' n n'} [Monadₓ m'] [MonadFunctorTₓ n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : OptionTₓ m' α).run = monadMap (@f) x.run :=
  rfl

end OptionTₓ

instance (m : Type u → Type v) [Monadₓ m] [IsLawfulMonad m] : IsLawfulMonad (OptionTₓ m) where
  id_map := by
    intros
    apply OptionTₓ.ext
    simp only [OptionTₓ.run_map]
    rw [map_ext_congr, id_map]
    intro a
    cases a <;> rfl
  bind_assoc := by
    intros
    apply OptionTₓ.ext
    simp only [OptionTₓ.run_bind, bind_assoc]
    rw [bind_ext_congr]
    intro a
    cases a <;> simp [OptionTₓ.bindCont]
  pure_bind := by
    intros <;> apply OptionTₓ.ext <;> simp [OptionTₓ.bindCont]

