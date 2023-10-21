/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
prelude
import Init.Data.Int.Basic
import Init.Data.Nat.Bitwise

#align_import init.data.int.bitwise from "leanprover-community/lean"@"cc811188929de043b8b159da1c49e72074f59db0"

universe u

namespace Int

#print Int.div2 /-
def div2 : ℤ → ℤ
  | of_nat n => n.div2
  | -[n+1] => -[n.div2+1]
#align int.div2 Int.div2
-/

#print Int.bodd /-
def bodd : ℤ → Bool
  | of_nat n => n.bodd
  | -[n+1] => not n.bodd
#align int.bodd Int.bodd
-/

#print Int.bit /-
def bit (b : Bool) : ℤ → ℤ :=
  cond b bit1 bit0
#align int.bit Int.bit
-/

#print Int.testBit /-
def testBit : ℤ → ℕ → Bool
  | (m : ℕ), n => Nat.testBit m n
  | -[m+1], n => not (Nat.testBit m n)
#align int.test_bit Int.testBit
-/

#print Int.natBitwise /-
def natBitwise (f : Bool → Bool → Bool) (m n : ℕ) : ℤ :=
  cond (f false false) -[Nat.bitwise (fun x y => not (f x y)) m n+1] (Nat.bitwise f m n)
#align int.nat_bitwise Int.natBitwise
-/

#print Int.bitwise /-
def bitwise (f : Bool → Bool → Bool) : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => natBitwise f m n
  | (m : ℕ), -[n+1] => natBitwise (fun x y => f x (not y)) m n
  | -[m+1], (n : ℕ) => natBitwise (fun x y => f (not x) y) m n
  | -[m+1], -[n+1] => natBitwise (fun x y => f (not x) (not y)) m n
#align int.bitwise Int.bitwise
-/

#print Int.lnot /-
def lnot : ℤ → ℤ
  | (m : ℕ) => -[m+1]
  | -[m+1] => m
#align int.lnot Int.lnot
-/

#print Int.lor /-
def lor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.lor m n
  | (m : ℕ), -[n+1] => -[Nat.ldiff n m+1]
  | -[m+1], (n : ℕ) => -[Nat.ldiff m n+1]
  | -[m+1], -[n+1] => -[Nat.land m n+1]
#align int.lor Int.lor
-/

#print Int.land /-
def land : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.land m n
  | (m : ℕ), -[n+1] => Nat.ldiff m n
  | -[m+1], (n : ℕ) => Nat.ldiff n m
  | -[m+1], -[n+1] => -[Nat.lor m n+1]
#align int.land Int.land
-/

#print Int.ldiff /-
def ldiff : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.ldiff m n
  | (m : ℕ), -[n+1] => Nat.land m n
  | -[m+1], (n : ℕ) => -[Nat.lor m n+1]
  | -[m+1], -[n+1] => Nat.ldiff n m
#align int.ldiff Int.ldiff
-/

#print Int.xor /-
def xor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.xor m n
  | (m : ℕ), -[n+1] => -[Nat.xor m n+1]
  | -[m+1], (n : ℕ) => -[Nat.xor m n+1]
  | -[m+1], -[n+1] => Nat.xor m n
#align int.lxor Int.xor
-/

#print ShiftLeft.shiftLeft /-
def shiftLeft : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.shiftl m n
  | (m : ℕ), -[n+1] => Nat.shiftr m (Nat.succ n)
  | -[m+1], (n : ℕ) => -[Nat.shiftLeft' true m n+1]
  | -[m+1], -[n+1] => -[Nat.shiftr m (Nat.succ n)+1]
#align int.shiftl ShiftLeft.shiftLeft
-/

#print ShiftRight.shiftRight /-
def shiftRight (m n : ℤ) : ℤ :=
  shiftLeft m (-n)
#align int.shiftr ShiftRight.shiftRight
-/

end Int

