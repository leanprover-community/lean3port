
#print Real /-
axiom Real : Type
#align real Real
-/

axiom Real.hasZero : Zero Real
#align real.has_zero Real.hasZero

axiom Real.hasOne : One Real
#align real.has_one Real.hasOne

axiom Real.hasAdd : Add Real
#align real.has_add Real.hasAdd

axiom Real.hasMul : Mul Real
#align real.has_mul Real.hasMul

axiom Real.hasSub : Sub Real
#align real.has_sub Real.hasSub

axiom Real.hasNeg : Neg Real
#align real.has_neg Real.hasNeg

axiom Real.hasDiv : Div Real
#align real.has_div Real.hasDiv

axiom Real.hasLt : LT Real
#align real.has_lt Real.hasLt

axiom Real.hasLe : LE Real
#align real.has_le Real.hasLe

attribute [instance]
  Real.hasZero Real.hasOne Real.hasAdd Real.hasMul Real.hasSub Real.hasNeg Real.hasDiv Real.hasLe Real.hasLt

axiom Real.ofInt : Int → Real
#align real.of_int Real.ofInt

axiom Real.toInt : Real → Int
#align real.to_int Real.toInt

axiom Real.IsInt : Real → Prop
#align real.is_int Real.IsInt

