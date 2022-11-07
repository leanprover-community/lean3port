prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.String.Basic

def Lean.version : Nat × Nat × Nat :=
  (3, 48, 0)

#print Lean.githash /-
def Lean.githash : String :=
  "283f6ed8083ab4dd7c36300f31816c5cb793f2f7"
-/

def Lean.isRelease : Bool :=
  1 ≠ 0

/-- Additional version description like "nightly-2018-03-11" -/
def Lean.specialVersionDesc : String :=
  ""

