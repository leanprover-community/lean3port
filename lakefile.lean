import Lake
open Lake DSL

package lean3port

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"f16c2788554b9960de815ae1e3f25de8c722bde4"

@[defaultTarget]
lean_lib Leanbin
