import Lake
open Lake DSL

package lean3port

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"107f2a66860a71eb30410f12f9a962eeb34d36a8"

@[defaultTarget]
lean_lib Leanbin
