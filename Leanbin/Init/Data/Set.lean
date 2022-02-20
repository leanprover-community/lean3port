/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Interactive
import Leanbin.Init.Control.Lawful

universe u v

def Set (α : Type u) :=
  α → Prop

def SetOf {α : Type u} (p : α → Prop) : Set α :=
  p

namespace Set

variable {α : Type u} {β : Type v}

protected def Mem (a : α) (s : Set α) :=
  s a

instance : HasMem α (Set α) :=
  ⟨Set.Mem⟩

protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

instance : HasSubset (Set α) :=
  ⟨Set.Subset⟩

protected def Sep (p : α → Prop) (s : Set α) : Set α :=
  { a | a ∈ s ∧ p a }

instance : HasSep α (Set α) :=
  ⟨Set.Sep⟩

instance : HasEmptyc (Set α) :=
  ⟨fun a => False⟩

def Univ : Set α := fun a => True

protected def Insert (a : α) (s : Set α) : Set α :=
  { b | b = a ∨ b ∈ s }

instance : HasInsert α (Set α) :=
  ⟨Set.Insert⟩

instance : HasSingleton α (Set α) :=
  ⟨fun a => { b | b = a }⟩

instance : IsLawfulSingleton α (Set α) :=
  ⟨fun a => funext fun b => propext <| or_falseₓ _⟩

protected def Union (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∨ a ∈ s₂ }

instance : HasUnion (Set α) :=
  ⟨Set.Union⟩

protected def Inter (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∧ a ∈ s₂ }

instance : HasInter (Set α) :=
  ⟨Set.Inter⟩

def Compl (s : Set α) : Set α :=
  { a | a ∉ s }

protected def Diff (s t : Set α) : Set α :=
  { a ∈ s | a ∉ t }

instance : HasSdiff (Set α) :=
  ⟨Set.Diff⟩

def Powerset (s : Set α) : Set (Set α) :=
  { t | t ⊆ s }

@[reducible]
def SUnion (s : Set (Set α)) : Set α :=
  { t | ∃ a ∈ s, t ∈ a }

def Image (f : α → β) (s : Set α) : Set β :=
  { b | ∃ a, a ∈ s ∧ f a = b }

instance : Functor Set where
  map := @Set.Image

instance : IsLawfulFunctor Set where
  id_map := fun _ s => funext fun b => propext ⟨fun ⟨_, sb, rfl⟩ => sb, fun sb => ⟨_, sb, rfl⟩⟩
  comp_map := fun _ _ _ g h s =>
    funext fun c =>
      propext
        ⟨fun ⟨a, ⟨h₁, h₂⟩⟩ => ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩, fun ⟨b, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ =>
          ⟨a,
            ⟨h₁, by
              dsimp <;> cc⟩⟩⟩

end Set

