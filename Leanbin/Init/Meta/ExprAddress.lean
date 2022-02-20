/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import Leanbin.Init.Meta.Expr
import Leanbin.Init.Data.List.Basic
import Leanbin.Init.Data.Option.Basic
import Leanbin.Init.Util

namespace Expr

/-- An enum representing a recursive argument in an `expr` constructor.
Types of local and meta variables are not included because they are not consistently set and
depend on context. -/
inductive Coord : Type
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
def code : Coord → ℕ
  | coord.app_fn => 0
  | coord.app_arg => 1
  | coord.lam_var_type => 2
  | coord.lam_body => 3
  | coord.pi_var_type => 4
  | coord.pi_body => 5
  | coord.elet_var_type => 6
  | coord.elet_assignment => 7
  | coord.elet_body => 8

protected def repr : Coord → Stringₓ
  | coord.app_fn => "app_fn"
  | coord.app_arg => "app_arg"
  | coord.lam_var_type => "lam_var_type"
  | coord.lam_body => "lam_body"
  | coord.pi_var_type => "pi_var_type"
  | coord.pi_body => "pi_body"
  | coord.elet_var_type => "elet_var_type"
  | coord.elet_assignment => "elet_assignment"
  | coord.elet_body => "elet_body"

instance : HasRepr Coord :=
  ⟨Coord.repr⟩

instance : HasToString Coord :=
  ⟨Coord.repr⟩

unsafe instance : has_to_format Coord :=
  ⟨format.of_string ∘ coord.repr⟩

unsafe instance has_dec_eq : DecidableEq Coord :=
  unchecked_cast (inferInstance : DecidableEq ℕ)

instance hasLt : LT Coord :=
  ⟨fun x y => x.code < y.code⟩

/-- Use this to pick the subexpression of a given expression that cooresponds
to the given coordinate. -/
unsafe def follow : Coord → expr → Option expr
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
def Address : Type :=
  List Coord

namespace Address

unsafe instance has_dec_eq : DecidableEq Address :=
  (inferInstance : DecidableEq (List Expr.Coord))

protected def toString : Address → Stringₓ :=
  toString ∘ List.map Coord.repr

instance hasRepr : HasRepr Address :=
  ⟨Address.toString⟩

instance hasToString : HasToString Address :=
  ⟨Address.toString⟩

unsafe instance has_to_format : has_to_format Address :=
  ⟨list.to_format⟩

instance : Append Address :=
  ⟨List.append⟩

/-- `as_below x y` is some z when it finds `∃ z, x = y ++ z` -/
unsafe def as_below : Address → Address → Option Address
  | a, [] => some a
  |-- [] ++ a = a
    [],
    _ => none
  |-- (h::t) ++ _ ≠ []
      -- if t₂ ++ z = t₁ then (h₁ :: t₁) ++ z = (h₁ :: t₂)
      h₁ ::
      t₁,
    h₂ :: t₂ => if h₁ = h₂ then as_below t₁ t₂ else none

unsafe def is_below : Address → Address → Bool
  | a₁, a₂ => Option.isSome <| as_below a₁ a₂

/-- `follow a e` finds the subexpression of `e` at the given address `a`. -/
unsafe def follow : Address → expr → Option expr
  | [], e => e
  | h :: t, e => coord.follow h e >>= follow t

end Address

end Expr

