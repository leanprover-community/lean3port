prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.String.Basic

def Lean.version : Nat × Nat × Nat :=
  (3, 45, 0)

def Lean.githashₓ : Stringₓ :=
  "22b09be35ef66aece11e6e8f5d114f42b064259b"

def Lean.isRelease : Bool :=
  1 ≠ 0

/-- Additional version description like "nightly-2018-03-11" -/
def Lean.specialVersionDesc : Stringₓ :=
  ""

