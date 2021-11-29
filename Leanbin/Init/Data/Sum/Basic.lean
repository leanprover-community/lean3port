prelude 
import Leanbin.Init.Logic

universe u v

variable {α : Type u} {β : Type v}

instance Sum.inhabitedLeftₓ [h : Inhabited α] : Inhabited (Sum α β) :=
  ⟨Sum.inl (default α)⟩

instance Sum.inhabitedRightₓ [h : Inhabited β] : Inhabited (Sum α β) :=
  ⟨Sum.inr (default β)⟩

