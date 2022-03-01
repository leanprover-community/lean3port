prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.String.Basic

def Lean.version : Nat × Nat × Nat :=
  (3, 40, 0)

def Lean.githashₓ : Stringₓ :=
  "82216a493580a309a04b02c2b6eb5f82f0aef192"

def Lean.isRelease : Bool :=
  1 ≠ 0

/-- Additional version description like "nightly-2018-03-11" -/
def Lean.specialVersionDesc : Stringₓ :=
  ""

