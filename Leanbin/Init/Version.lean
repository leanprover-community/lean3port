prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.String.Basic

def Lean.version : Nat × Nat × Nat :=
  (3, 47, 0)

def Lean.githashₓ : Stringₓ :=
  "4f9b974353ea684c98ec938f91f3a526218503ed"

def Lean.isRelease : Bool :=
  1 ≠ 0

/-- Additional version description like "nightly-2018-03-11" -/
def Lean.specialVersionDesc : Stringₓ :=
  ""

