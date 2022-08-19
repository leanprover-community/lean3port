/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Extensional equality for functions, and a proof of function extensionality from quotients.
-/
prelude
import Leanbin.Init.Data.Quot
import Leanbin.Init.Logic

variable {α : Sort u} {β : α → Sort v}

namespace Function

protected theorem Equiv.is_equivalence (α : Sort u) (β : α → Sort v) : Equivalence (@Function.Equiv α β) :=
  mk_equivalence (@Function.Equiv α β) (@Equiv.refl α β) (@Equiv.symm α β) (@Equiv.trans α β)

end Function

