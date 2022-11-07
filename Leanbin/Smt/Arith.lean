
axiom Real : Type

#print Zero /-
axiom Zero : Zero Real
-/

#print One /-
axiom One : One Real
-/

#print Add /-
axiom Add : Add Real
-/

#print Mul /-
axiom Mul : Mul Real
-/

#print Sub /-
axiom Sub : Sub Real
-/

#print Neg /-
axiom Neg : Neg Real
-/

#print Div /-
axiom Div : Div Real
-/

#print LT /-
axiom LT : LT Real
-/

#print LE /-
axiom LE : LE Real
-/

attribute [instance]
  Real.hasZero Real.hasOne Real.hasAdd Real.hasMul Real.hasSub Real.hasNeg Real.hasDiv Real.hasLe Real.hasLt

axiom of_int : Int → Real

axiom to_int : Real → Int

axiom is_int : Real → Prop

