/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.String.Basic
import Leanbin.Init.Data.Bool.Basic
import Leanbin.Init.Data.Subtype.Basic
import Leanbin.Init.Data.Unsigned.Basic
import Leanbin.Init.Data.Prod
import Leanbin.Init.Data.Sum.Basic
import Leanbin.Init.Data.Nat.Div
import Leanbin.Init.Data.Repr

open Sum Subtype Nat

universe u v

/-- Convert the object into a string for tracing/display purposes.
Similar to Haskell's `show`.
See also `has_repr`, which is used to output a string which is a valid lean code.
See also `has_to_format` and `has_to_tactic_format`, `format` has additional support for colours and pretty printing multilines.
 -/
abbrev HasToString := ToString

instance : HasToString Unsigned :=
  ⟨fun n => toString n.val⟩

