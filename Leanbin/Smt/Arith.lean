
axiom Real : Type

axiom Zero : Zero Real

axiom One : One Real

axiom Add : Add Real

axiom Mul : Mul Real

axiom Sub : Sub Real

axiom Neg : Neg Real

axiom Div : Div Real

axiom LT : LT Real

axiom LE : LE Real

attribute [instance]
  Real.hasZero Real.hasOne Real.hasAdd Real.hasMul Real.hasSub Real.hasNeg Real.hasDiv Real.hasLe Real.hasLt

axiom of_int : Int → Real

axiom to_int : Real → Int

axiom is_int : Real → Prop

