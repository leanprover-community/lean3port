prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.String.Basic

def Lean.version : Nat × Nat × Nat :=
  (3, 46, 0)

def Lean.githashₓ : Stringₓ :=
  "741670c439f1ca266bc7fe61ef7212cc9afd9dd8"

def Lean.isRelease : Bool :=
  1 ≠ 0

/-- Additional version description like "nightly-2018-03-11" -/
def Lean.specialVersionDesc : Stringₓ :=
  ""

