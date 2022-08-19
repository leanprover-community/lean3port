/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Core

/-!
# Boolean operations
-/


/-- Boolean OR -/
@[simp] abbrev bor := or

/-- Boolean AND -/
@[simp] abbrev band := and

/-- Boolean NOT -/
@[simp] abbrev bnot := not

/-- Boolean XOR -/
@[inline]
def bxor : Bool → Bool → Bool
  | true, false => true
  | false, true => true
  | _, _ => false

