prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.String.Basic

def Lean.version : Nat × Nat × Nat :=
  (3, 50, 3)
#align lean.version Lean.version

#print Lean.githash /-
def Lean.githash : String :=
  "855e5b74e3a52a40552e8f067169d747d48743fd"
#align lean.githash Lean.githash
-/

def Lean.isRelease : Bool :=
  1 ≠ 0
#align lean.is_release Lean.isRelease

/-- Additional version description like "nightly-2018-03-11" -/
def Lean.specialVersionDesc : String :=
  ""
#align lean.special_version_desc Lean.specialVersionDesc

