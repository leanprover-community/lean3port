
axiom Real : Type
#align real Real

#print Zero /-
axiom Zero : Zero Real
#align has_zero Zero
-/

#print One /-
axiom One : One Real
#align has_one One
-/

#print Add /-
axiom Add : Add Real
#align has_add Add
-/

#print Mul /-
axiom Mul : Mul Real
#align has_mul Mul
-/

#print Sub /-
axiom Sub : Sub Real
#align has_sub Sub
-/

#print Neg /-
axiom Neg : Neg Real
#align has_neg Neg
-/

#print Div /-
axiom Div : Div Real
#align has_div Div
-/

#print LT /-
axiom LT : LT Real
#align has_lt LT
-/

#print LE /-
axiom LE : LE Real
#align has_le LE
-/

attribute [instance]
  Real.hasZero Real.hasOne Real.hasAdd Real.hasMul Real.hasSub Real.hasNeg Real.hasDiv Real.hasLe Real.hasLt

axiom of_int : Int → Real
#align of_int of_int

axiom to_int : Real → Int
#align to_int to_int

axiom is_int : Real → Prop
#align is_int is_int

