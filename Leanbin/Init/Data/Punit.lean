prelude
import Leanbin.Init.Logic

theorem punit_eq (a b : PUnit) : a = b :=
  PUnit.recOn a (PUnit.recOn b rfl)

theorem punit_eq_star (a : PUnit) : a = PUnit.unit :=
  punit_eq a PUnit.unit

instance : Subsingleton PUnit :=
  Subsingleton.intro punit_eq

instance : Inhabited PUnit :=
  ⟨PUnit.unit⟩

instance : DecidableEq PUnit := fun a b => is_true (punit_eq a b)

