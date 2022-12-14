/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.ac_tactics
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Tactic

namespace Tactic

-- (flat_assoc op assoc e)
unsafe axiom flat_assoc : expr → expr → expr → tactic (expr × expr)
#align tactic.flat_assoc tactic.flat_assoc

-- (perm_ac op assoc comm e1 e2) Try to construct a proof that e1 = e2 modulo AC
unsafe axiom perm_ac : expr → expr → expr → expr → expr → tactic expr
#align tactic.perm_ac tactic.perm_ac

end Tactic

