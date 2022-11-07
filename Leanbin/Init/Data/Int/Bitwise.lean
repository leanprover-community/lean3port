/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
prelude
import Leanbin.Init.Data.Int.Basic
import Leanbin.Init.Data.Nat.Bitwise

universe u

namespace Int

def div2 : ℤ → ℤ
  | of_nat n => n.div2
  | -[n+1] => -[n.div2+1]

def bodd : ℤ → Bool
  | of_nat n => n.bodd
  | -[n+1] => not n.bodd

def bit (b : Bool) : ℤ → ℤ :=
  cond b bit1 bit0

def testBit : ℤ → ℕ → Bool
  | (m : ℕ), n => Nat.testBit m n
  | -[m+1], n => not (Nat.testBit m n)

def natBitwise (f : Bool → Bool → Bool) (m n : ℕ) : ℤ :=
  cond (f false false) -[Nat.bitwise (fun x y => not (f x y)) m n+1] (Nat.bitwise f m n)

def bitwise (f : Bool → Bool → Bool) : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => natBitwise f m n
  | (m : ℕ), -[n+1] => natBitwise (fun x y => f x (not y)) m n
  | -[m+1], (n : ℕ) => natBitwise (fun x y => f (not x) y) m n
  | -[m+1], -[n+1] => natBitwise (fun x y => f (not x) (not y)) m n

def lnot : ℤ → ℤ
  | (m : ℕ) => -[m+1]
  | -[m+1] => m

def lor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.lor m n
  | (m : ℕ), -[n+1] => -[Nat.ldiff n m+1]
  | -[m+1], (n : ℕ) => -[Nat.ldiff m n+1]
  | -[m+1], -[n+1] => -[Nat.land m n+1]

def land : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.land m n
  | (m : ℕ), -[n+1] => Nat.ldiff m n
  | -[m+1], (n : ℕ) => Nat.ldiff n m
  | -[m+1], -[n+1] => -[Nat.lor m n+1]

def ldiff : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.ldiff m n
  | (m : ℕ), -[n+1] => Nat.land m n
  | -[m+1], (n : ℕ) => -[Nat.lor m n+1]
  | -[m+1], -[n+1] => Nat.ldiff n m

def lxor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.lxor m n
  | (m : ℕ), -[n+1] => -[Nat.lxor m n+1]
  | -[m+1], (n : ℕ) => -[Nat.lxor m n+1]
  | -[m+1], -[n+1] => Nat.lxor m n

def shiftl : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.shiftl m n
  | (m : ℕ), -[n+1] => Nat.shiftr m (Nat.succ n)
  | -[m+1], (n : ℕ) => -[Nat.shiftl' true m n+1]
  | -[m+1], -[n+1] => -[Nat.shiftr m (Nat.succ n)+1]

def shiftr (m n : ℤ) : ℤ :=
  shiftl m (-n)

end Int

