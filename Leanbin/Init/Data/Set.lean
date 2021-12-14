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

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
protected def sep ( p : α → Prop ) ( s : Set α ) : Set α := { a | a ∈ s ∧ p a }

instance : HasSep α (Set α) :=
  ⟨Set.Sep⟩

instance : HasEmptyc (Set α) :=
  ⟨fun a => False⟩

def univ : Set α :=
  fun a => True

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
protected def insert ( a : α ) ( s : Set α ) : Set α := { b | b = a ∨ b ∈ s }

instance : HasInsert α (Set α) :=
  ⟨Set.Insert⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
instance : HasSingleton α Set α := ⟨ fun a => { b | b = a } ⟩

instance : IsLawfulSingleton α (Set α) :=
  ⟨fun a => funext$ fun b => propext$ or_falseₓ _⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
protected def union ( s₁ s₂ : Set α ) : Set α := { a | a ∈ s₁ ∨ a ∈ s₂ }

instance : HasUnion (Set α) :=
  ⟨Set.Union⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
protected def inter ( s₁ s₂ : Set α ) : Set α := { a | a ∈ s₁ ∧ a ∈ s₂ }

instance : HasInter (Set α) :=
  ⟨Set.Inter⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
def compl ( s : Set α ) : Set α := { a | a ∉ s }

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
protected def diff ( s t : Set α ) : Set α := { a ∈ s | a ∉ t }

instance : HasSdiff (Set α) :=
  ⟨Set.Diff⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
def powerset ( s : Set α ) : Set Set α := { t | t ⊆ s }

prefix:100 "𝒫" => powerset

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » s)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
@[ reducible ] def sUnion ( s : Set Set α ) : Set α := { t | ∃ ( a : _ ) ( _ : a ∈ s ) , t ∈ a }

prefix:110 "⋃₀" => sUnion

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
def image ( f : α → β ) ( s : Set α ) : Set β := { b | ∃ a , a ∈ s ∧ f a = b }

instance : Functor Set :=
  { map := @Set.Image }

instance : IsLawfulFunctor Set :=
  { id_map := fun _ s => funext$ fun b => propext ⟨fun ⟨_, sb, rfl⟩ => sb, fun sb => ⟨_, sb, rfl⟩⟩,
    comp_map :=
      fun _ _ _ g h s =>
        funext$
          fun c =>
            propext
              ⟨fun ⟨a, ⟨h₁, h₂⟩⟩ => ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
                fun ⟨b, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ =>
                  ⟨a,
                    ⟨h₁,
                      by 
                        dsimp <;> cc⟩⟩⟩ }

end Set

