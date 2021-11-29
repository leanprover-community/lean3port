prelude 
import Leanbin.Init.Control.Lift

universe u

@[inline]
def idBind {α β : Type u} (x : α) (f : α → id β) : id β :=
  f x

@[inline]
instance : Monadₓ.{u, u} id :=
  { pure := @id, bind := @idBind }

@[inline]
instance : MonadRun id id :=
  ⟨@id⟩

