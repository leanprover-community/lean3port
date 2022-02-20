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


/-- `cond b x y` is `x` if `b = tt` and `y` otherwise. -/
@[inline]
def cond.{u} {a : Type u} : Bool → a → a → a
  | tt, x, y => x
  | ff, x, y => y

/-- Boolean OR -/
@[inline]
def bor : Bool → Bool → Bool
  | tt, b => true
  | ff, b => b

/-- Boolean AND -/
@[inline]
def band : Bool → Bool → Bool
  | tt, b => b
  | ff, b => false

/-- Boolean NOT -/
@[inline]
def bnot : Bool → Bool
  | tt => false
  | ff => true

/-- Boolean XOR -/
@[inline]
def bxor : Bool → Bool → Bool
  | tt, ff => true
  | ff, tt => true
  | _, _ => false

