/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Name

universe u

unsafe axiom options : Type

unsafe axiom options.size : options → Nat

unsafe axiom options.mk : options

unsafe axiom options.contains : options → Name → Bool

unsafe axiom options.set_bool : options → Name → Bool → options

unsafe axiom options.set_nat : options → Name → Nat → options

unsafe axiom options.set_string : options → Name → Stringₓ → options

unsafe axiom options.get_bool : options → Name → Bool → Bool

unsafe axiom options.get_nat : options → Name → Nat → Nat

unsafe axiom options.get_string : options → Name → Stringₓ → Stringₓ

unsafe axiom options.join : options → options → options

unsafe axiom options.fold {α : Type u} : options → α → (Name → α → α) → α

unsafe axiom options.has_decidable_eq : DecidableEq options

attribute [instance] options.has_decidable_eq

unsafe instance : Add options :=
  ⟨options.join⟩

unsafe instance : Inhabited options :=
  ⟨options.mk⟩

