prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.String.Basic

def Lean.version : Nat × Nat × Nat :=
  (3, 49, 0)
#align lean.version Lean.version

#print Lean.githash /-
def Lean.githash : String :=
  "acf633e01a8783a12060b0a1b7b5b5e15fd73e77"
#align lean.githash Lean.githash
-/

def Lean.isRelease : Bool :=
  1 ≠ 0
#align lean.is_release Lean.isRelease

/-- Additional version description like "nightly-2018-03-11" -/
def Lean.specialVersionDesc : String :=
  ""
#align lean.special_version_desc Lean.specialVersionDesc

