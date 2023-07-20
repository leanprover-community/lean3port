-- Authors: E.W.Ayers 
prelude
import Leanbin.Init.Data.Default

#align_import init.meta.float from "leanprover-community/lean"@"9dc6b1ea9d64cb163b0a0c371622887d32e6792f"

namespace Native

unsafe axiom float : Type
#align native.float native.float

namespace Float

-- fixed values based on the underlying C++ float implementation.
namespace Specification

/-- The base. Either 2 or 10. -/
unsafe axiom radix : Nat
#align native.float.specification.radix native.float.specification.radix

/-- The length of the mantissa. -/
unsafe axiom precision : Nat
#align native.float.specification.precision native.float.specification.precision

/-- The maximum exponent. -/
unsafe axiom emax : Nat
#align native.float.specification.emax native.float.specification.emax

/-- The minimum exponent. `= 1 - emax` -/
unsafe axiom emin : Int
#align native.float.specification.emin native.float.specification.emin

end Specification

open Specification

/--
Returns the difference between 1.0 and the next representable value of the given floating-point type.
    Reference: https://en.cppreference.com/w/cpp/types/numeric_limits/epsilon
 -/
unsafe axiom epsilon : float
#align native.float.epsilon native.float.epsilon

/-- returns the maximum rounding error -/
unsafe axiom round_error : float
#align native.float.round_error native.float.round_error

/-- Positive infinity. -/
unsafe axiom infinity : float
#align native.float.infinity native.float.infinity

/-- Quiet NaN. -/
unsafe axiom qNaN : float
#align native.float.qNaN native.float.qNaN

/-- Signalling NaN. -/
unsafe axiom sNaN : float
#align native.float.sNaN native.float.sNaN

/-- Returns true when the value is positive or negative infinity.-/
unsafe axiom is_infinite : float → Bool
#align native.float.is_infinite native.float.is_infinite

unsafe axiom is_finite : float → Bool
#align native.float.is_finite native.float.is_finite

/-- Returns true when the value is qNaN or sNaN-/
unsafe axiom is_nan : float → Bool
#align native.float.is_nan native.float.is_nan

/-- Reference: https://en.cppreference.com/w/cpp/numeric/math/isnormal
    https://stackoverflow.com/questions/8341395/what-is-a-subnormal-floating-point-number
-/
unsafe axiom is_normal : float → Bool
#align native.float.is_normal native.float.is_normal

/-- The sign `s` of the float. `tt` if negative. -/
unsafe axiom sign : float → Bool
#align native.float.sign native.float.sign

/--
The exponent `e` of the float in the base given by `radix`. `emin ≤ e ≤ emax`. Returns none if the number is not finite.  -/
unsafe axiom exponent : float → Option Int
#align native.float.exponent native.float.exponent

/--
Decompose the number `f` in to `(s,e)` where `0.5 ≤ s < 1.0` and `emin ≤ e ≤ emax` such that `f = s * 2 ^ e`. -/
unsafe axiom frexp : float → float × Int
#align native.float.frexp native.float.frexp

/-- Decompose in to integer `fst` and fractional `snd` parts. -/
unsafe axiom modf : float → float × float
#align native.float.modf native.float.modf

/--
`mantissa f` returns a number `s` where `0.5 ≤ s < 1.0` such that there exists an integer `e` such that `f = s * 2 ^ e` -/
unsafe def mantissa : float → float :=
  Prod.fst ∘ frexp
#align native.float.mantissa native.float.mantissa

-- [TODO]
-- /-- List of digits in the mantissa of the float. `d₀.d₁d₂d₃ ⋯`
--     The length is `precision` and `0 ≤ dᵢ < radix` for each digit `dᵢ`.
--     The head of the list is the most significant digit.
--      -/
-- meta constant mantissa_digits : float → array precision nat
unsafe axiom add : float → float → float
#align native.float.add native.float.add

unsafe instance : Add float :=
  ⟨add⟩

unsafe axiom sub : float → float → float
#align native.float.sub native.float.sub

unsafe instance : Sub float :=
  ⟨sub⟩

unsafe axiom neg : float → float
#align native.float.neg native.float.neg

unsafe instance : Neg float :=
  ⟨neg⟩

unsafe axiom mul : float → float → float
#align native.float.mul native.float.mul

unsafe instance : Mul float :=
  ⟨mul⟩

unsafe axiom div : float → float → float
#align native.float.div native.float.div

unsafe instance : Div float :=
  ⟨div⟩

/-- remainder of the floating point division operation. -/
unsafe axiom fmod : float → float → float
#align native.float.fmod native.float.fmod

/-- signed remainder of the division operation. -/
unsafe axiom remainder : float → float → float
#align native.float.remainder native.float.remainder

unsafe axiom max : float → float → float
#align native.float.max native.float.max

unsafe axiom min : float → float → float
#align native.float.min native.float.min

unsafe axiom pow : float → float → float
#align native.float.pow native.float.pow

unsafe instance has_float_pow : Pow float float :=
  ⟨pow⟩
#align native.float.has_float_pow native.float.has_float_pow

/-- Square root. -/
unsafe axiom sqrt : float → float
#align native.float.sqrt native.float.sqrt

/-- Cube root. -/
unsafe axiom cbrt : float → float
#align native.float.cbrt native.float.cbrt

/-- Computes `sqrt(x^2 + y^2)`. -/
unsafe axiom hypot : float → float → float
#align native.float.hypot native.float.hypot

/-- Exponential function. -/
unsafe axiom exp : float → float
#align native.float.exp native.float.exp

/-- 2 raised to the given power. -/
unsafe axiom exp2 : float → float
#align native.float.exp2 native.float.exp2

/-- Natural logarithm. -/
unsafe axiom log : float → float
#align native.float.log native.float.log

unsafe axiom log2 : float → float
#align native.float.log2 native.float.log2

unsafe axiom log10 : float → float
#align native.float.log10 native.float.log10

unsafe axiom pi : float
#align native.float.pi native.float.pi

unsafe axiom sin : float → float
#align native.float.sin native.float.sin

unsafe axiom cos : float → float
#align native.float.cos native.float.cos

unsafe axiom tan : float → float
#align native.float.tan native.float.tan

unsafe axiom asin : float → float
#align native.float.asin native.float.asin

unsafe axiom acos : float → float
#align native.float.acos native.float.acos

unsafe axiom atan : float → float
#align native.float.atan native.float.atan

/-- `atan2 y x` finds the angle anticlockwise from the x-axis to the point `[x,y]`.-/
unsafe axiom atan2 : float → float → float
#align native.float.atan2 native.float.atan2

unsafe axiom sinh : float → float
#align native.float.sinh native.float.sinh

unsafe axiom cosh : float → float
#align native.float.cosh native.float.cosh

unsafe axiom tanh : float → float
#align native.float.tanh native.float.tanh

unsafe axiom asinh : float → float
#align native.float.asinh native.float.asinh

unsafe axiom acosh : float → float
#align native.float.acosh native.float.acosh

unsafe axiom atanh : float → float
#align native.float.atanh native.float.atanh

unsafe axiom abs : float → float
#align native.float.abs native.float.abs

/-- Nearest integer not less than the given value.
Returns 0 if the input is not finite. -/
unsafe axiom ceil : float → Int
#align native.float.ceil native.float.ceil

/-- Nearest integer not greater than the given value.
Returns 0 if the input is not finite. -/
unsafe axiom floor : float → Int
#align native.float.floor native.float.floor

/-- Nearest integer not greater in magnitude than the given value.
Returns 0 if the input is not finite. -/
unsafe axiom trunc : float → Int
#align native.float.trunc native.float.trunc

/-- Round to the nearest integer, rounding away from zero in halfway cases.
Returns 0 if the input is not finite. -/
unsafe axiom round : float → Int
#align native.float.round native.float.round

unsafe axiom lt : float → float → Bool
#align native.float.lt native.float.lt

unsafe instance : LT float :=
  ⟨fun x y => lt x y⟩

unsafe instance decidable_lt : DecidableRel float.has_lt.lt := by infer_instance
#align native.float.decidable_lt native.float.decidable_lt

unsafe axiom le : float → float → Bool
#align native.float.le native.float.le

unsafe instance : LE float :=
  ⟨fun x y => le x y⟩

unsafe instance decidable_le : DecidableRel float.has_le.le := by infer_instance
#align native.float.decidable_le native.float.decidable_le

unsafe axiom dec_eq : DecidableEq float
#align native.float.dec_eq native.float.dec_eq

attribute [instance] dec_eq

unsafe axiom of_nat : Nat → float
#align native.float.of_nat native.float.of_nat

unsafe axiom of_int : Int → float
#align native.float.of_int native.float.of_int

unsafe instance of_nat_coe : Coe Nat float :=
  ⟨of_nat⟩
#align native.float.of_nat_coe native.float.of_nat_coe

unsafe instance of_int_coe : Coe Int float :=
  ⟨of_int⟩
#align native.float.of_int_coe native.float.of_int_coe

protected unsafe def zero : float :=
  of_nat 0
#align native.float.zero native.float.zero

protected unsafe def one : float :=
  of_nat 1
#align native.float.one native.float.one

unsafe instance : Zero float :=
  ⟨float.zero⟩

unsafe instance : One float :=
  ⟨float.one⟩

unsafe axiom to_repr : float → String
#align native.float.to_repr native.float.to_repr

unsafe instance : Repr float :=
  ⟨to_repr⟩

unsafe instance : ToString float :=
  ⟨to_repr⟩

unsafe instance : has_to_format float :=
  ⟨format.of_string ∘ toString⟩

unsafe axiom of_string : String → Option float
#align native.float.of_string native.float.of_string

unsafe instance has_nat_pow : Pow float Nat :=
  ⟨fun a b => native.float.pow a (float.of_nat b)⟩
#align native.float.has_nat_pow native.float.has_nat_pow

end Float

end Native

