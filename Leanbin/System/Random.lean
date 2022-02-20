/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

universe u

/-
Basic random number generator support based on the one
available on the Haskell library
-/
-- Interface for random number generators.
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

-- "Standard" random number generator.
structure StdGen where
  s1 : Nat
  s2 : Nat

def stdRange :=
  (1, 2147483562)

instance : HasRepr StdGen where
  repr := fun ⟨s1, s2⟩ => "⟨" ++ toString s1 ++ ", " ++ toString s2 ++ "⟩"

def stdNextₓ : StdGen → Nat × StdGen
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

def stdSplitₓ : StdGen → StdGen × StdGen
  | g@⟨s1, s2⟩ =>
    let new_s1 := if s1 = 2147483562 then 1 else s1 + 1
    let new_s2 := if s2 = 1 then 2147483398 else s2 - 1
    let new_g := (stdNextₓ g).2
    let left_g := StdGen.mk new_s1 new_g.2
    let right_g := StdGen.mk new_g.1 new_s2
    (left_g, right_g)

instance : RandomGen StdGen where
  range := fun _ => stdRange
  next := stdNextₓ
  split := stdSplitₓ

/-- Return a standard number generator. -/
def mkStdGenₓ (s : Nat := 0) : StdGen :=
  let q := s / 2147483562
  let s1 := s % 2147483562
  let s2 := q % 2147483398
  ⟨s1 + 1, s2 + 1⟩

/-
Auxiliary function for random_nat_val.
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
    have : r' / gen_mag - 1 < r' := by
      by_cases' h : (r + 1) / gen_mag = 0
      · rw [h]
        simp
        apply Nat.zero_lt_succₓ
        
      · have : (r + 1) / gen_mag > 0 := Nat.pos_of_ne_zeroₓ h
        have h₁ : (r + 1) / gen_mag - 1 < (r + 1) / gen_mag := by
          apply Nat.sub_ltₓ
          assumption
          run_tac
            tactic.comp_val
        have h₂ : (r + 1) / gen_mag ≤ r + 1 := by
          apply Nat.div_le_selfₓ
        exact lt_of_lt_of_leₓ h₁ h₂
        
    rand_nat_aux (r' / gen_mag - 1) v' g'

/-- Generate a random natural number in the interval [lo, hi]. -/
def randNatₓ {gen : Type u} [RandomGen gen] (g : gen) (lo hi : Nat) : Nat × gen :=
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
  let (v, g') := randNatAuxₓ gen_lo gen_mag (Nat.zero_lt_succₓ _) tgt_mag 0 g
  let v' := lo' + v % k
  (v', g')

/-- Generate a random Boolean. -/
def randBoolₓ {gen : Type u} [RandomGen gen] (g : gen) : Bool × gen :=
  let (v, g') := randNatₓ g 0 1
  (v = 1, g')

