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

protected def mem (a : α) (s : Set α) :=
  s a

instance : HasMem α (Set α) :=
  ⟨Set.Mem⟩

protected def subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

instance : HasSubset (Set α) :=
  ⟨Set.Subset⟩

protected def sep (p : α → Prop) (s : Set α) : Set α :=
  { a | a ∈ s ∧ p a }

instance : HasSep α (Set α) :=
  ⟨Set.Sep⟩

instance : HasEmptyc (Set α) :=
  ⟨fun a => False⟩

def univ : Set α := fun a => True

protected def insert (a : α) (s : Set α) : Set α :=
  { b | b = a ∨ b ∈ s }

instance : HasInsert α (Set α) :=
  ⟨Set.Insert⟩

instance : HasSingleton α (Set α) :=
  ⟨fun a => { b | b = a }⟩

instance : IsLawfulSingleton α (Set α) :=
  ⟨fun a => funext $ fun b => propext $ or_falseₓ _⟩

protected def union (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∨ a ∈ s₂ }

instance : HasUnion (Set α) :=
  ⟨Set.Union⟩

protected def inter (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∧ a ∈ s₂ }

instance : HasInter (Set α) :=
  ⟨Set.Inter⟩

def compl (s : Set α) : Set α :=
  { a | a ∉ s }

protected def diff (s t : Set α) : Set α :=
  { a ∈ s | a ∉ t }

instance : HasSdiff (Set α) :=
  ⟨Set.Diff⟩

def powerset (s : Set α) : Set (Set α) :=
  { t | t ⊆ s }

prefix:100 "𝒫" => powerset

@[reducible]
def sUnion (s : Set (Set α)) : Set α :=
  { t | ∃ a ∈ s, t ∈ a }

prefix:110 "⋃₀" => sUnion

def image (f : α → β) (s : Set α) : Set β :=
  { b | ∃ a, a ∈ s ∧ f a = b }

instance : Functor Set where
  map := @Set.Image

instance : IsLawfulFunctor Set where
  id_map := fun _ s => funext $ fun b => propext ⟨fun ⟨_, sb, rfl⟩ => sb, fun sb => ⟨_, sb, rfl⟩⟩
  comp_map := fun _ _ _ g h s =>
    funext $ fun c =>
      propext
        ⟨fun ⟨a, ⟨h₁, h₂⟩⟩ => ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩, fun ⟨b, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ =>
          ⟨a,
            ⟨h₁, by
              dsimp <;> cc⟩⟩⟩

end Set

