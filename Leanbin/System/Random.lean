/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module system.random
! leanprover-community/lean commit 4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

universe u

/-!
# Basic random number generator support

based on the one available on the Haskell library
-/


#print RandomGen /-
/-- Interface for random number generators. -/
class RandomGen (g : Type u) where
  /- `range` returns the range of values returned by
      the generator. -/
  range : g → Nat × Nat
  /- `next` operation returns a natural number that is uniformly distributed
      the range returned by `range` (including both end points),
     and a new generator. -/
  next : g → Nat × g
  /-
    The 'split' operation allows one to obtain two distinct random number
    generators. This is very useful in functional programs (for example, when
    passing a random number generator down to recursive calls). -/
  split : g → g × g
#align random_gen RandomGen
-/

#print StdGen /-
/-- "Standard" random number generator. -/
structure StdGen where
  s1 : Nat
  s2 : Nat
#align std_gen StdGen
-/

#print stdRange /-
def stdRange :=
  (1, 2147483562)
#align std_range stdRange
-/

instance : Repr StdGen
    where repr := fun ⟨s1, s2⟩ => "⟨" ++ toString s1 ++ ", " ++ toString s2 ++ "⟩"

def stdNext : StdGen → Nat × StdGen
  | ⟨s1, s2⟩ =>
    let k : Int := s1 / 53668
    let s1' : Int := 40014 * ((s1 : Int) - k * 53668) - k * 12211
    let s1'' : Int := if s1' < 0 then s1' + 2147483563 else s1'
    let k' : Int := s2 / 52774
    let s2' : Int := 40692 * ((s2 : Int) - k' * 52774) - k' * 3791
    let s2'' : Int := if s2' < 0 then s2' + 2147483399 else s2'
    let z : Int := s1'' - s2''
    let z' : Int := if z < 1 then z + 2147483562 else z % 2147483562
    (z'.toNat, ⟨s1''.toNat, s2''.toNat⟩)
#align std_next stdNextₓ

def stdSplit : StdGen → StdGen × StdGen
  | g@⟨s1, s2⟩ =>
    let new_s1 := if s1 = 2147483562 then 1 else s1 + 1
    let new_s2 := if s2 = 1 then 2147483398 else s2 - 1
    let new_g := (stdNext g).2
    let left_g := StdGen.mk new_s1 new_g.2
    let right_g := StdGen.mk new_g.1 new_s2
    (left_g, right_g)
#align std_split stdSplitₓ

instance : RandomGen StdGen where
  range _ := stdRange
  next := stdNext
  split := stdSplit

#print mkStdGen /-
/-- Return a standard number generator. -/
def mkStdGen (s : Nat := 0) : StdGen :=
  let q := s / 2147483562
  let s1 := s % 2147483562
  let s2 := q % 2147483398
  ⟨s1 + 1, s2 + 1⟩
#align mk_std_gen mkStdGen
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.comp_val -/
/-- Auxiliary function for random_nat_val.
Generate random values until we exceed the target magnitude.
`gen_lo` and `gen_mag` are the generator lower bound and magnitude.
The parameter `r` is the "remaining" magnitude.
-/
private def rand_nat_aux {gen : Type u} [RandomGen gen] (gen_lo gen_mag : Nat) (h : gen_mag > 0) :
    Nat → Nat → gen → Nat × gen
  | 0, v, g => (v, g)
  | r'@(r + 1), v, g =>
    let (x, g') := RandomGen.next g
    let v' := v * gen_mag + (x - gen_lo)
    have : r' / gen_mag - 1 < r' :=
      by
      by_cases h : (r + 1) / gen_mag = 0
      · rw [h]
        simp
        apply Nat.zero_lt_succ
      · have : (r + 1) / gen_mag > 0 := Nat.pos_of_ne_zero h
        have h₁ : (r + 1) / gen_mag - 1 < (r + 1) / gen_mag :=
          by
          apply Nat.sub_lt
          assumption
          run_tac
            tactic.comp_val
        have h₂ : (r + 1) / gen_mag ≤ r + 1 := by apply Nat.div_le_self
        exact lt_of_lt_of_le h₁ h₂
    rand_nat_aux (r' / gen_mag - 1) v' g'

#print randNat /-
/-- Generate a random natural number in the interval [lo, hi]. -/
def randNat {gen : Type u} [RandomGen gen] (g : gen) (lo hi : Nat) : Nat × gen :=
  let lo' := if lo > hi then hi else lo
  let hi' := if lo > hi then lo else hi
  let (gen_lo, gen_hi) := RandomGen.range g
  let gen_mag := gen_hi - gen_lo + 1
  let
    q :=/-
          Probabilities of the most likely and least likely result
          will differ at most by a factor of (1 +- 1/q).  Assuming the RandomGen
          is uniform, of course
        -/
    1000
  let k := hi' - lo' + 1
  let tgt_mag := k * q
  let (v, g') := randNatAux gen_lo gen_mag (Nat.zero_lt_succ _) tgt_mag 0 g
  let v' := lo' + v % k
  (v', g')
#align rand_nat randNat
-/

#print randBool /-
/-- Generate a random Boolean. -/
def randBool {gen : Type u} [RandomGen gen] (g : gen) : Bool × gen :=
  let (v, g') := randNat g 0 1
  (v = 1, g')
#align rand_bool randBool
-/

