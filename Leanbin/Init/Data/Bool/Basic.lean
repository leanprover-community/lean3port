prelude
import Leanbin.Init.Core

/-!
# Boolean operations
-/


/-- `cond b x y` is `x` if `b = tt` and `y` otherwise. -/
@[inline]
def cond.{u} {a : Type u} : Bool → a → a → a
  | tt, x, y => x
  | ff, x, y => y

/-- Boolean OR -/
@[inline]
def bor : Bool → Bool → Bool
  | tt, b => tt
  | ff, b => b

/-- Boolean AND -/
@[inline]
def band : Bool → Bool → Bool
  | tt, b => b
  | ff, b => ff

/-- Boolean NOT -/
@[inline]
def bnot : Bool → Bool
  | tt => ff
  | ff => tt

/-- Boolean XOR -/
@[inline]
def bxor : Bool → Bool → Bool
  | tt, ff => tt
  | ff, tt => tt
  | _, _ => ff

