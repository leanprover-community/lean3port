/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta.Tactic

#align_import init.meta.ac_tactics from "leanprover-community/lean"@"148da46481df09ac36e5d55497ae0f3754534914"

namespace Tactic

-- (flat_assoc op assoc e)
unsafe axiom flat_assoc : expr → expr → expr → tactic (expr × expr)
#align tactic.flat_assoc tactic.flat_assoc

-- (perm_ac op assoc comm e1 e2) Try to construct a proof that e1 = e2 modulo AC
unsafe axiom perm_ac : expr → expr → expr → expr → expr → tactic expr
#align tactic.perm_ac tactic.perm_ac

end Tactic

