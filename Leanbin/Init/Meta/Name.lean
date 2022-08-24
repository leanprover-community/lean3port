/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Ordering.Basic
import Leanbin.Init.Coe
import Leanbin.Init.Data.ToString

/-- Reflect a C++ name object. The VM replaces it with the C++ implementation. -/
inductive Name
  | anonymous : Name
  | mk_string : Stringₓ → Name → Name
  | mk_numeral : Unsigned → Name → Name

/-- Gadget for automatic parameter support. This is similar to the opt_param gadget, but it uses
    the tactic declaration names tac_name to synthesize the argument.
    Like opt_param, this gadget only affects elaboration.
    For example, the tactic will *not* be invoked during type class resolution. -/
@[reducible]
def AutoParam.{u} (α : Sort u) (tac_name : Name) : Sort u :=
  α

@[simp]
theorem auto_param_eq.{u} (α : Sort u) (n : Name) : AutoParam α n = α :=
  rfl

instance : Inhabited Name :=
  ⟨Name.anonymous⟩

def mkStrName (n : Name) (s : Stringₓ) : Name :=
  Name.mk_string s n

def mkNumName (n : Name) (v : Nat) : Name :=
  Name.mk_numeral (Unsigned.ofNat' v) n

def mkSimpleName (s : Stringₓ) : Name :=
  mkStrName Name.anonymous s

instance stringToName : Coe Stringₓ Name :=
  ⟨mkSimpleName⟩

open Name

def Name.getPrefix : Name → Name
  | anonymous => anonymous
  | mk_string s p => p
  | mk_numeral s p => p

def Name.updatePrefix : Name → Name → Name
  | anonymous, new_p => anonymous
  | mk_string s p, new_p => mk_string s new_p
  | mk_numeral s p, new_p => mk_numeral s new_p

-- ./././Mathport/Syntax/Translate/Basic.lean:335:40: warning: unsupported option eqn_compiler.ite
-- Without this option, we get errors when defining the following definitions.
set_option eqn_compiler.ite false

def Name.toStringWithSep (sep : Stringₓ) : Name → Stringₓ
  | anonymous => "[anonymous]"
  | mk_string s anonymous => s
  | mk_numeral v anonymous => reprₓ v
  | mk_string s n => Name.toStringWithSep n ++ sep ++ s
  | mk_numeral v n => Name.toStringWithSep n ++ sep ++ reprₓ v

private def name.components' : Name → List Name
  | anonymous => []
  | mk_string s n => mk_string s anonymous :: name.components' n
  | mk_numeral v n => mk_numeral v anonymous :: name.components' n

def Name.components (n : Name) : List Name :=
  (Name.components' n).reverse

protected def Name.toString : Name → Stringₓ :=
  Name.toStringWithSep "."

protected def Name.repr (n : Name) : Stringₓ :=
  "`" ++ n.toString

instance : HasToString Name :=
  ⟨Name.toString⟩

instance : HasRepr Name :=
  ⟨Name.repr⟩

-- TODO(Leo): provide a definition in Lean.
unsafe axiom name.has_decidable_eq : DecidableEq Name

-- Both cmp and lex_cmp are total orders, but lex_cmp implements a lexicographical order.
unsafe axiom name.cmp : Name → Name → Ordering

unsafe axiom name.lex_cmp : Name → Name → Ordering

unsafe axiom name.append : Name → Name → Name

unsafe axiom name.is_internal : Name → Bool

protected unsafe def name.lt (a b : Name) : Prop :=
  name.cmp a b = Ordering.lt

unsafe instance : DecidableRel name.lt := fun a b => Ordering.decidableEq _ _

unsafe instance : LT Name :=
  ⟨name.lt⟩

attribute [instance] name.has_decidable_eq

unsafe instance : Append Name :=
  ⟨name.append⟩

/-- `name.append_after n i` return a name of the form n_i -/
unsafe axiom name.append_after : Name → Nat → Name

unsafe def name.is_prefix_of : Name → Name → Bool
  | p, Name.anonymous => false
  | p, n => if p = n then true else name.is_prefix_of p n.getPrefix

unsafe def name.is_suffix_of : Name → Name → Bool
  | anonymous, _ => true
  | mk_string s n, mk_string s' n' => s = s' && name.is_suffix_of n n'
  | mk_numeral v n, mk_numeral v' n' => v = v' && name.is_suffix_of n n'
  | _, _ => false

unsafe def name.replace_prefix : Name → Name → Name → Name
  | anonymous, p, p' => anonymous
  | mk_string s c, p, p' => if c = p then mk_string s p' else mk_string s (name.replace_prefix c p p')
  | mk_numeral v c, p, p' => if c = p then mk_numeral v p' else mk_numeral v (name.replace_prefix c p p')

