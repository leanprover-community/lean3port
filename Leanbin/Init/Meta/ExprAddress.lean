/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers

! This file was ported from Lean 3 source module init.meta.expr_address
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
#align expr.coord Expr.Coord

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
#align expr.coord.code Expr.Coord.code

protected def repr : Coord → String
  | coord.app_fn => "app_fn"
  | coord.app_arg => "app_arg"
  | coord.lam_var_type => "lam_var_type"
  | coord.lam_body => "lam_body"
  | coord.pi_var_type => "pi_var_type"
  | coord.pi_body => "pi_body"
  | coord.elet_var_type => "elet_var_type"
  | coord.elet_assignment => "elet_assignment"
  | coord.elet_body => "elet_body"
#align expr.coord.repr Expr.Coord.repr

instance : Repr Coord :=
  ⟨Coord.repr⟩

instance : ToString Coord :=
  ⟨Coord.repr⟩

unsafe instance : has_to_format Coord :=
  ⟨format.of_string ∘ coord.repr⟩

unsafe instance has_dec_eq : DecidableEq Coord :=
  unchecked_cast (inferInstance : DecidableEq ℕ)
#align expr.coord.has_dec_eq expr.coord.has_dec_eq

instance hasLt : LT Coord :=
  ⟨fun x y => x.code < y.code⟩
#align expr.coord.has_lt Expr.Coord.hasLt

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
#align expr.coord.follow expr.coord.follow

end Coord

/-- An address is a list of coordinates used to reference subterms of an expression.
The first coordinate in the list corresponds to the root of the expression. -/
def Address : Type :=
  List Coord
#align expr.address Expr.Address

namespace Address

unsafe instance has_dec_eq : DecidableEq Address :=
  (inferInstance : DecidableEq (List Expr.Coord))
#align expr.address.has_dec_eq expr.address.has_dec_eq

protected def toString : Address → String :=
  toString ∘ List.map Coord.repr
#align expr.address.to_string Expr.Address.toString

instance hasRepr : Repr Address :=
  ⟨Address.toString⟩
#align expr.address.has_repr Expr.Address.hasRepr

instance hasToString : ToString Address :=
  ⟨Address.toString⟩
#align expr.address.has_to_string Expr.Address.hasToString

unsafe instance has_to_format : has_to_format Address :=
  ⟨list.to_format⟩
#align expr.address.has_to_format expr.address.has_to_format

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
#align expr.address.as_below expr.address.as_below

unsafe def is_below : Address → Address → Bool
  | a₁, a₂ => Option.isSome <| as_below a₁ a₂
#align expr.address.is_below expr.address.is_below

/-- `follow a e` finds the subexpression of `e` at the given address `a`. -/
unsafe def follow : Address → expr → Option expr
  | [], e => e
  | h :: t, e => coord.follow h e >>= follow t
#align expr.address.follow expr.address.follow

end Address

end Expr

