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
  | mk_string : String → Name → Name
  | mk_numeral : Unsigned → Name → Name
#align name Name

/-- Gadget for automatic parameter support. This is similar to the opt_param gadget, but it uses
    the tactic declaration names tac_name to synthesize the argument.
    Like opt_param, this gadget only affects elaboration.
    For example, the tactic will *not* be invoked during type class resolution. -/
@[reducible]
def autoParam.{u} (α : Sort u) (tac_name : Name) : Sort u :=
  α
#align auto_param autoParamₓ

@[simp]
theorem auto_param_eq.{u} (α : Sort u) (n : Name) : autoParam α n = α :=
  rfl
#align auto_param_eq auto_param_eq

instance : Inhabited Name :=
  ⟨Name.anonymous⟩

def mkStrName (n : Name) (s : String) : Name :=
  Name.mk_string s n
#align mk_str_name mkStrName

def mkNumName (n : Name) (v : Nat) : Name :=
  Name.mk_numeral (Unsigned.ofNat' v) n
#align mk_num_name mkNumName

def mkSimpleName (s : String) : Name :=
  mkStrName Name.anonymous s
#align mk_simple_name mkSimpleName

instance stringToName : Coe String Name :=
  ⟨mkSimpleName⟩
#align string_to_name stringToName

open Name

def Name.getPrefix : Name → Name
  | anonymous => anonymous
  | mk_string s p => p
  | mk_numeral s p => p
#align name.get_prefix Name.getPrefix

def Name.updatePrefix : Name → Name → Name
  | anonymous, new_p => anonymous
  | mk_string s p, new_p => mk_string s new_p
  | mk_numeral s p, new_p => mk_numeral s new_p
#align name.update_prefix Name.updatePrefix

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option eqn_compiler.ite -/
-- Without this option, we get errors when defining the following definitions.
set_option eqn_compiler.ite false

def Name.toStringWithSep (sep : String) : Name → String
  | anonymous => "[anonymous]"
  | mk_string s anonymous => s
  | mk_numeral v anonymous => repr v
  | mk_string s n => Name.toStringWithSep n ++ sep ++ s
  | mk_numeral v n => Name.toStringWithSep n ++ sep ++ repr v
#align name.to_string_with_sep Name.toStringWithSep

private def name.components' : Name → List Name
  | anonymous => []
  | mk_string s n => mk_string s anonymous :: name.components' n
  | mk_numeral v n => mk_numeral v anonymous :: name.components' n
#align name.components' name.components'

def Name.components (n : Name) : List Name :=
  (Name.components' n).reverse
#align name.components Name.components

protected def Name.toString : Name → String :=
  Name.toStringWithSep "."
#align name.to_string Name.toString

protected def Name.repr (n : Name) : String :=
  "`" ++ n.toString
#align name.repr Name.repr

instance : ToString Name :=
  ⟨Name.toString⟩

instance : Repr Name :=
  ⟨Name.repr⟩

-- TODO(Leo): provide a definition in Lean.
unsafe axiom name.has_decidable_eq : DecidableEq Name
#align name.has_decidable_eq name.has_decidable_eq

/-! Both cmp and lex_cmp are total orders, but lex_cmp implements a lexicographical order. -/


unsafe axiom name.cmp : Name → Name → Ordering
#align name.cmp name.cmp

unsafe axiom name.lex_cmp : Name → Name → Ordering
#align name.lex_cmp name.lex_cmp

unsafe axiom name.append : Name → Name → Name
#align name.append name.append

unsafe axiom name.is_internal : Name → Bool
#align name.is_internal name.is_internal

protected unsafe def name.lt (a b : Name) : Prop :=
  name.cmp a b = Ordering.lt
#align name.lt name.lt

unsafe instance : DecidableRel name.lt := fun a b => Ordering.decidableEq _ _

unsafe instance : LT Name :=
  ⟨name.lt⟩

attribute [instance] name.has_decidable_eq

unsafe instance : Append Name :=
  ⟨name.append⟩

/-- `name.append_after n i` return a name of the form n_i -/
unsafe axiom name.append_after : Name → Nat → Name
#align name.append_after name.append_after

unsafe def name.is_prefix_of : Name → Name → Bool
  | p, Name.anonymous => false
  | p, n => if p = n then true else name.is_prefix_of p n.getPrefix
#align name.is_prefix_of name.is_prefix_of

unsafe def name.is_suffix_of : Name → Name → Bool
  | anonymous, _ => true
  | mk_string s n, mk_string s' n' => s = s' && name.is_suffix_of n n'
  | mk_numeral v n, mk_numeral v' n' => v = v' && name.is_suffix_of n n'
  | _, _ => false
#align name.is_suffix_of name.is_suffix_of

unsafe def name.replace_prefix : Name → Name → Name → Name
  | anonymous, p, p' => anonymous
  | mk_string s c, p, p' => if c = p then mk_string s p' else mk_string s (name.replace_prefix c p p')
  | mk_numeral v c, p, p' => if c = p then mk_numeral v p' else mk_numeral v (name.replace_prefix c p p')
#align name.replace_prefix name.replace_prefix

