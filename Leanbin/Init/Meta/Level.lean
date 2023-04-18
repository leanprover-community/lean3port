/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.level
! leanprover-community/lean commit ab383aec6bf581badb383037f744bfbc600f4e4c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Name
import Leanbin.Init.Meta.Format

/--
A type universe term. eg `max u v`. Reflect a C++ level object. The VM replaces it with the C++ implementation. -/
unsafe inductive level
  | zero : level
  | succ : level → level
  | max : level → level → level
  | imax : level → level → level
  | param : Name → level
  | mvar : Name → level
#align level level

unsafe instance : Inhabited level :=
  ⟨level.zero⟩

-- TODO(Leo): provide a definition in Lean.
unsafe axiom level.has_decidable_eq : DecidableEq level
#align level.has_decidable_eq level.has_decidable_eq

attribute [instance] level.has_decidable_eq

unsafe axiom level.lt : level → level → Bool
#align level.lt level.lt

unsafe axiom level.lex_lt : level → level → Bool
#align level.lex_lt level.lex_lt

unsafe axiom level.fold {α : Type} : level → α → (level → α → α) → α
#align level.fold level.fold

/-- Return the given level expression normal form -/
unsafe axiom level.normalize : level → level
#align level.normalize level.normalize

/-- Return tt iff lhs and rhs denote the same level.
   The check is done by normalization. -/
unsafe axiom level.eqv : level → level → Bool
#align level.eqv level.eqv

/-- Return tt iff the first level occurs in the second -/
unsafe axiom level.occurs : level → level → Bool
#align level.occurs level.occurs

/-- Replace a parameter named n with l in the first level if the list contains the pair (n, l) -/
unsafe axiom level.instantiate : level → List (Name × level) → level
#align level.instantiate level.instantiate

unsafe axiom level.to_format : level → options → format
#align level.to_format level.to_format

unsafe axiom level.to_string : level → String
#align level.to_string level.to_string

unsafe instance : ToString level :=
  ⟨level.to_string⟩

unsafe instance : has_to_format level :=
  ⟨fun l => level.to_format l options.mk⟩

unsafe def level.of_nat : Nat → level
  | 0 => level.zero
  | Nat.succ n => level.succ (level.of_nat n)
#align level.of_nat level.of_nat

unsafe def level.has_param : level → Name → Bool
  | level.succ l, n => level.has_param l n
  | level.max l₁ l₂, n => level.has_param l₁ n || level.has_param l₂ n
  | level.imax l₁ l₂, n => level.has_param l₁ n || level.has_param l₂ n
  | level.param n₁, n => n₁ = n
  | l, n => false
#align level.has_param level.has_param

