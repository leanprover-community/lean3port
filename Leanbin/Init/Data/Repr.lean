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

open Sum Subtype Nat

universe u v

abbrev HasRepr := Repr

namespace Nat

def digitSucc (base : ℕ) : List ℕ → List ℕ
  | [] => [1]
  | d :: ds => if d + 1 = base then 0 :: digitSucc base ds else (d + 1) :: ds

end Nat

def charToHex (c : Char) : String :=
  let n := Char.toNat c
  let d2 := n / 16
  let d1 := n % 16
  hexDigitRepr d2 ++ hexDigitRepr d1

