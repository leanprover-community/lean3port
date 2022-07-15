prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.String.Basic

def Lean.version : Nat × Nat × Nat :=
  (3, 44, 1)

def Lean.githashₓ : Stringₓ :=
  "9d5adc6ab80d02bb2a0fd39a786aaeb1efd6fb01"

def Lean.isRelease : Bool :=
  1 ≠ 0

/-- Additional version description like "nightly-2018-03-11" -/
def Lean.specialVersionDesc : Stringₓ :=
  ""

