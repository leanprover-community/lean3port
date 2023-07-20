prelude
import Leanbin.Init.Data.Nat.Basic
import Leanbin.Init.Data.String.Basic

#align_import init.version from "leanprover-community/lean"@"cce7990ea86a78bdb383e38ed7f9b5ba93c60ce0"

def Lean.version : Nat × Nat × Nat :=
  (3, 51, 1)
#align lean.version Lean.version

#print Lean.githash /-
def Lean.githash : String :=
  "cce7990ea86a78bdb383e38ed7f9b5ba93c60ce0"
#align lean.githash Lean.githash
-/

def Lean.isRelease : Bool :=
  1 ≠ 0
#align lean.is_release Lean.isRelease

/-- Additional version description like "nightly-2018-03-11" -/
def Lean.specialVersionDesc : String :=
  ""
#align lean.special_version_desc Lean.specialVersionDesc

