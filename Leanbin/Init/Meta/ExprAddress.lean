prelude
import Leanbin.Init.Meta.Expr
import Leanbin.Init.Data.List.Basic
import Leanbin.Init.Data.Option.Basic
import Leanbin.Init.Util

namespace Expr

/-- An enum representing a recursive argument in an `expr` constructor.
Types of local and meta variables are not included because they are not consistently set and
depend on context. -/
inductive coord : Type
  | app_fn
  | app_arg
  | lam_var_type
  | lam_body
  | pi_var_type
  | pi_body
  | elet_var_type
  | elet_assignment
  | elet_body

namespace Coord

/-- Convert the coord enum to its index number. -/
def code : coord → ℕ
  | coord.app_fn => 0
  | coord.app_arg => 1
  | coord.lam_var_type => 2
  | coord.lam_body => 3
  | coord.pi_var_type => 4
  | coord.pi_body => 5
  | coord.elet_var_type => 6
  | coord.elet_assignment => 7
  | coord.elet_body => 8

protected def reprₓ : coord → Stringₓ
  | coord.app_fn => "app_fn"
  | coord.app_arg => "app_arg"
  | coord.lam_var_type => "lam_var_type"
  | coord.lam_body => "lam_body"
  | coord.pi_var_type => "pi_var_type"
  | coord.pi_body => "pi_body"
  | coord.elet_var_type => "elet_var_type"
  | coord.elet_assignment => "elet_assignment"
  | coord.elet_body => "elet_body"

instance : HasRepr coord :=
  ⟨coord.repr⟩

instance : HasToString coord :=
  ⟨coord.repr⟩

unsafe instance : has_to_format coord :=
  ⟨format.of_string ∘ coord.repr⟩

unsafe instance has_dec_eq : DecidableEq coord :=
  unchecked_cast (inferInstance : DecidableEq ℕ)

instance LT : LT coord :=
  ⟨fun x y => x.code < y.code⟩

/-- Use this to pick the subexpression of a given expression that cooresponds
to the given coordinate. -/
unsafe def follow : coord → expr → Option expr
  | coord.app_fn, expr.app f _ => some f
  | coord.app_arg, expr.app _ a => some a
  | coord.lam_var_type, expr.lam n bi y _ => some y
  | coord.lam_body, expr.lam n bi _ b => some b
  | coord.pi_var_type, expr.pi n bi y _ => some y
  | coord.pi_body, expr.pi n bi _ b => some b
  | coord.elet_var_type, expr.elet n y _ _ => some y
  | coord.elet_assignment, expr.elet n _ a _ => some a
  | coord.elet_body, expr.elet n _ _ b => some b
  | _, _ => none

end Coord

/-- An address is a list of coordinates used to reference subterms of an expression.
The first coordinate in the list corresponds to the root of the expression. -/
def address : Type :=
  List coord

namespace Address

unsafe instance has_dec_eq : DecidableEq address :=
  (inferInstance : DecidableEq (List Expr.Coord))

protected def toString : address → Stringₓ :=
  toString ∘ List.map coord.repr

instance HasRepr : HasRepr address :=
  ⟨address.to_string⟩

instance HasToString : HasToString address :=
  ⟨address.to_string⟩

unsafe instance has_to_format : has_to_format address :=
  ⟨list.to_format⟩

instance : Append address :=
  ⟨List.append⟩

/-- `as_below x y` is some z when it finds `∃ z, x = y ++ z` -/
unsafe def as_below : address → address → Option address
  | a, [] => some a
  | [], _ => none
  | h₁ :: t₁, h₂ :: t₂ => if h₁ = h₂ then as_below t₁ t₂ else none

unsafe def is_below : address → address → Bool
  | a₁, a₂ => Option.isSome $ as_below a₁ a₂

/-- `follow a e` finds the subexpression of `e` at the given address `a`. -/
unsafe def follow : address → expr → Option expr
  | [], e => e
  | h :: t, e => coord.follow h e >>= follow t

end Address

end Expr

