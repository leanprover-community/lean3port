-- Authors: E.W.Ayers 
prelude
import Leanbin.Init.Data.Default

namespace Native

unsafe axiom float : Type

namespace Float

-- fixed values based on the underlying C++ float implementation.
namespace Specification

/-- The base. Either 2 or 10. -/
unsafe axiom radix : Nat

/-- The length of the mantissa. -/
unsafe axiom precision : Nat

/-- The maximum exponent. -/
unsafe axiom emax : Nat

/-- The minimum exponent. `= 1 - emax` -/
unsafe axiom emin : Int

end Specification

open Specification

/-- Returns the difference between 1.0 and the next representable value of the given floating-point type.
    Reference: https://en.cppreference.com/w/cpp/types/numeric_limits/epsilon
 -/
unsafe axiom epsilon : float

/-- returns the maximum rounding error -/
unsafe axiom round_error : float

/-- Positive infinity. -/
unsafe axiom infinity : float

/-- Quiet NaN. -/
unsafe axiom qNaN : float

/-- Signalling NaN. -/
unsafe axiom sNaN : float

/-- Returns true when the value is positive or negative infinity.-/
unsafe axiom is_infinite : float → Bool

unsafe axiom is_finite : float → Bool

/-- Returns true when the value is qNaN or sNaN-/
unsafe axiom is_nan : float → Bool

/-- Reference: https://en.cppreference.com/w/cpp/numeric/math/isnormal
    https://stackoverflow.com/questions/8341395/what-is-a-subnormal-floating-point-number
-/
unsafe axiom is_normal : float → Bool

/-- The sign `s` of the float. `tt` if negative. -/
unsafe axiom sign : float → Bool

/--
The exponent `e` of the float in the base given by `radix`. `emin ≤ e ≤ emax`. Returns none if the number is not finite.  -/
unsafe axiom exponent : float → Option Int

/-- Decompose the number `f` in to `(s,e)` where `0.5 ≤ s < 1.0` and `emin ≤ e ≤ emax` such that `f = s * 2 ^ e`. -/
unsafe axiom frexp : float → float × Int

/-- Decompose in to integer `fst` and fractional `snd` parts. -/
unsafe axiom modf : float → float × float

/--
`mantissa f` returns a number `s` where `0.5 ≤ s < 1.0` such that there exists an integer `e` such that `f = s * 2 ^ e` -/
unsafe def mantissa : float → float :=
  Prod.fst ∘ frexp

-- [TODO]
-- /-- List of digits in the mantissa of the float. `d₀.d₁d₂d₃ ⋯`
--     The length is `precision` and `0 ≤ dᵢ < radix` for each digit `dᵢ`.
--     The head of the list is the most significant digit.
--      -/
-- meta constant mantissa_digits : float → array precision nat
unsafe axiom add : float → float → float

unsafe instance : Add float :=
  ⟨add⟩

unsafe axiom sub : float → float → float

unsafe instance : Sub float :=
  ⟨sub⟩

unsafe axiom neg : float → float

unsafe instance : Neg float :=
  ⟨neg⟩

unsafe axiom mul : float → float → float

unsafe instance : Mul float :=
  ⟨mul⟩

unsafe axiom div : float → float → float

unsafe instance : Div float :=
  ⟨div⟩

/-- remainder of the floating point division operation. -/
unsafe axiom fmod : float → float → float

/-- signed remainder of the division operation. -/
unsafe axiom remainder : float → float → float

unsafe axiom max : float → float → float

unsafe axiom min : float → float → float

unsafe axiom pow : float → float → float

unsafe instance has_float_pow : Pow float float :=
  ⟨pow⟩

/-- Square root. -/
unsafe axiom sqrt : float → float

/-- Cube root. -/
unsafe axiom cbrt : float → float

/-- Computes `sqrt(x^2 + y^2)`. -/
unsafe axiom hypot : float → float → float

/-- Exponential function. -/
unsafe axiom exp : float → float

/-- 2 raised to the given power. -/
unsafe axiom exp2 : float → float

/-- Natural logarithm. -/
unsafe axiom log : float → float

unsafe axiom log2 : float → float

unsafe axiom log10 : float → float

unsafe axiom pi : float

unsafe axiom sin : float → float

unsafe axiom cos : float → float

unsafe axiom tan : float → float

unsafe axiom asin : float → float

unsafe axiom acos : float → float

unsafe axiom atan : float → float

/-- `atan2 y x` finds the angle anticlockwise from the x-axis to the point `[x,y]`.-/
unsafe axiom atan2 : float → float → float

unsafe axiom sinh : float → float

unsafe axiom cosh : float → float

unsafe axiom tanh : float → float

unsafe axiom asinh : float → float

unsafe axiom acosh : float → float

unsafe axiom atanh : float → float

unsafe axiom abs : float → float

/-- Nearest integer not less than the given value. -/
unsafe axiom ceil : float → Int

/-- Nearest integer not greater than the given value. -/
unsafe axiom floor : float → Int

/-- Nearest integer not greater in magnitude than the given value. -/
unsafe axiom trunc : float → Int

/-- Round to the nearest integer, rounding away from zero in halfway cases. -/
unsafe axiom round : float → Int

unsafe axiom lt : float → float → Bool

unsafe instance : LT float :=
  ⟨fun x y => lt x y⟩

unsafe instance decidable_lt : DecidableRel float.has_lt.lt := by
  infer_instance

unsafe axiom le : float → float → Bool

unsafe instance : LE float :=
  ⟨fun x y => le x y⟩

unsafe instance decidable_le : DecidableRel float.has_le.le := by
  infer_instance

unsafe axiom dec_eq : DecidableEq float

attribute [instance] dec_eq

unsafe axiom of_nat : Nat → float

unsafe axiom of_int : Int → float

unsafe instance of_nat_coe : Coe Nat float :=
  ⟨of_nat⟩

unsafe instance of_int_coe : Coe Int float :=
  ⟨of_int⟩

protected unsafe def zero : float :=
  of_nat 0

protected unsafe def one : float :=
  of_nat 1

unsafe instance : Zero float :=
  ⟨float.zero⟩

unsafe instance : One float :=
  ⟨float.one⟩

unsafe axiom to_repr : float → Stringₓ

unsafe instance : HasRepr float :=
  ⟨to_repr⟩

unsafe instance : HasToString float :=
  ⟨to_repr⟩

unsafe instance : has_to_format float :=
  ⟨format.of_string ∘ toString⟩

unsafe axiom of_string : Stringₓ → Option float

unsafe instance has_nat_pow : Pow float Nat :=
  ⟨fun a b => native.float.pow a (float.of_nat b)⟩

end Float

end Native

