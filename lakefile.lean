import Lake
open Lake DSL

package lean3port where
  extraDepTargets := #[]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"380fbe124708314e7dcd6c3b8f41adffd5046c44"

@[defaultTarget]
lean_lib Leanbin
