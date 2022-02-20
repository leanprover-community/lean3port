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
  | -[1+ n] => -[1+ n.div2]

def bodd : ℤ → Bool
  | of_nat n => n.bodd
  | -[1+ n] => bnot n.bodd

def bit (b : Bool) : ℤ → ℤ :=
  cond b bit1 bit0

def testBit : ℤ → ℕ → Bool
  | (m : ℕ), n => Nat.testBit m n
  | -[1+ m], n => bnot (Nat.testBit m n)

def natBitwise (f : Bool → Bool → Bool) (m n : ℕ) : ℤ :=
  cond (f false false) -[1+ Nat.bitwiseₓ (fun x y => bnot (f x y)) m n] (Nat.bitwiseₓ f m n)

def bitwise (f : Bool → Bool → Bool) : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => natBitwise f m n
  | (m : ℕ), -[1+ n] => natBitwise (fun x y => f x (bnot y)) m n
  | -[1+ m], (n : ℕ) => natBitwise (fun x y => f (bnot x) y) m n
  | -[1+ m], -[1+ n] => natBitwise (fun x y => f (bnot x) (bnot y)) m n

def lnot : ℤ → ℤ
  | (m : ℕ) => -[1+ m]
  | -[1+ m] => m

def lor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.lorₓ m n
  | (m : ℕ), -[1+ n] => -[1+ Nat.ldiff n m]
  | -[1+ m], (n : ℕ) => -[1+ Nat.ldiff m n]
  | -[1+ m], -[1+ n] => -[1+ Nat.landₓ m n]

def land : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.landₓ m n
  | (m : ℕ), -[1+ n] => Nat.ldiff m n
  | -[1+ m], (n : ℕ) => Nat.ldiff n m
  | -[1+ m], -[1+ n] => -[1+ Nat.lorₓ m n]

def ldiff : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.ldiff m n
  | (m : ℕ), -[1+ n] => Nat.landₓ m n
  | -[1+ m], (n : ℕ) => -[1+ Nat.lorₓ m n]
  | -[1+ m], -[1+ n] => Nat.ldiff n m

def lxor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.lxor m n
  | (m : ℕ), -[1+ n] => -[1+ Nat.lxor m n]
  | -[1+ m], (n : ℕ) => -[1+ Nat.lxor m n]
  | -[1+ m], -[1+ n] => Nat.lxor m n

def shiftl : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.shiftl m n
  | (m : ℕ), -[1+ n] => Nat.shiftr m (Nat.succ n)
  | -[1+ m], (n : ℕ) => -[1+ Nat.shiftl' true m n]
  | -[1+ m], -[1+ n] => -[1+ Nat.shiftr m (Nat.succ n)]

def shiftr (m n : ℤ) : ℤ :=
  shiftl m (-n)

end Int

