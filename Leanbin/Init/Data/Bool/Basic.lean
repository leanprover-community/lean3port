/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.bool.basic
! leanprover-community/lean commit de855f9965c69f6818f97edaea7d937e24ef678a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Core

/-!
# Boolean operations
-/


#print cond /-
/-- `cond b x y` is `x` if `b = tt` and `y` otherwise. -/
@[inline]
def cond.{u} {a : Type u} : Bool → a → a → a
  | tt, x, y => x
  | ff, x, y => y
#align cond cond
-/

#print or /-
/-- Boolean OR -/
@[inline]
def or : Bool → Bool → Bool
  | tt, b => true
  | ff, b => b
#align bor or
-/

#print and /-
/-- Boolean AND -/
@[inline]
def and : Bool → Bool → Bool
  | tt, b => b
  | ff, b => false
#align band and
-/

#print not /-
/-- Boolean NOT -/
@[inline]
def not : Bool → Bool
  | tt => false
  | ff => true
#align bnot not
-/

#print xor /-
/-- Boolean XOR -/
@[inline]
def xor : Bool → Bool → Bool
  | tt, ff => true
  | ff, tt => true
  | _, _ => false
#align bxor xor
-/

