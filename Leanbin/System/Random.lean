
universe u

class RandomGen (g : Type u) where 
  range : g → Nat × Nat 
  next : g → Nat × g 
  split : g → g × g

structure StdGen where 
  s1 : Nat 
  s2 : Nat

def stdRange :=
  (1, 2147483562)

instance : HasRepr StdGen :=
  { repr := fun ⟨s1, s2⟩ => "⟨" ++ toString s1 ++ ", " ++ toString s2 ++ "⟩" }

def stdNextₓ : StdGen → Nat × StdGen
| ⟨s1, s2⟩ =>
  let k : Int := s1 / 53668
  let s1' : Int := (40014*(s1 : Int) - k*53668) - k*12211
  let s1'' : Int := if s1' < 0 then s1'+2147483563 else s1' 
  let k' : Int := s2 / 52774
  let s2' : Int := (40692*(s2 : Int) - k'*52774) - k'*3791
  let s2'' : Int := if s2' < 0 then s2'+2147483399 else s2' 
  let z : Int := s1'' - s2'' 
  let z' : Int := if z < 1 then z+2147483562 else z % 2147483562
  (z'.to_nat, ⟨s1''.to_nat, s2''.to_nat⟩)

def stdSplitₓ : StdGen → StdGen × StdGen
| g@⟨s1, s2⟩ =>
  let new_s1 := if s1 = 2147483562 then 1 else s1+1
  let new_s2 := if s2 = 1 then 2147483398 else s2 - 1
  let new_g := (stdNextₓ g).2
  let left_g := StdGen.mk new_s1 new_g.2
  let right_g := StdGen.mk new_g.1 new_s2
  (left_g, right_g)

instance : RandomGen StdGen :=
  { range := fun _ => stdRange, next := stdNextₓ, split := stdSplitₓ }

/-- Return a standard number generator. -/
def mkStdGenₓ (s : Nat := 0) : StdGen :=
  let q := s / 2147483562
  let s1 := s % 2147483562
  let s2 := q % 2147483398
  ⟨s1+1, s2+1⟩

-- error in System.Random: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
def rand_nat_aux
{gen : Type u}
[random_gen gen]
(gen_lo gen_mag : nat)
(h : «expr > »(gen_mag, 0)) : nat → nat → gen → «expr × »(nat, gen)
| 0, v, g := (v, g)
| r'@«expr + »(r, 1), v, g := let (x, g') := random_gen.next g,
    v' := «expr + »(«expr * »(v, gen_mag), «expr - »(x, gen_lo)) in
have «expr < »(«expr - »(«expr / »(r', gen_mag), 1), r'), begin
  by_cases [expr h, ":", expr «expr = »(«expr / »(«expr + »(r, 1), gen_mag), 0)],
  { rw ["[", expr h, "]"] [],
    simp [] [] [] [] [] [],
    apply [expr nat.zero_lt_succ] },
  { have [] [":", expr «expr > »(«expr / »(«expr + »(r, 1), gen_mag), 0)] [],
    from [expr nat.pos_of_ne_zero h],
    have [ident h₁] [":", expr «expr < »(«expr - »(«expr / »(«expr + »(r, 1), gen_mag), 1), «expr / »(«expr + »(r, 1), gen_mag))] [],
    { apply [expr nat.sub_lt],
      assumption,
      tactic.comp_val },
    have [ident h₂] [":", expr «expr ≤ »(«expr / »(«expr + »(r, 1), gen_mag), «expr + »(r, 1))] [],
    { apply [expr nat.div_le_self] },
    exact [expr lt_of_lt_of_le h₁ h₂] }
end,
rand_nat_aux «expr - »(«expr / »(r', gen_mag), 1) v' g'

/-- Generate a random natural number in the interval [lo, hi]. -/
def randNatₓ {gen : Type u} [RandomGen gen] (g : gen) (lo hi : Nat) : Nat × gen :=
  let lo' := if lo > hi then hi else lo 
  let hi' := if lo > hi then lo else hi 
  let (gen_lo, gen_hi) := RandomGen.range g 
  let gen_mag := (gen_hi - gen_lo)+1
  let q := 1000
  let k := (hi' - lo')+1
  let tgt_mag := k*q 
  let (v, g') := rand_nat_aux gen_lo gen_mag (Nat.zero_lt_succₓ _) tgt_mag 0 g 
  let v' := lo'+v % k
  (v', g')

/-- Generate a random Boolean. -/
def randBoolₓ {gen : Type u} [RandomGen gen] (g : gen) : Bool × gen :=
  let (v, g') := randNatₓ g 0 1
  (v = 1, g')

