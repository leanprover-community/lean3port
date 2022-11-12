/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Name

universe u

unsafe axiom options : Type
#align options options

unsafe axiom options.size : options → Nat
#align options.size options.size

unsafe axiom options.mk : options
#align options.mk options.mk

unsafe axiom options.contains : options → Name → Bool
#align options.contains options.contains

unsafe axiom options.set_bool : options → Name → Bool → options
#align options.set_bool options.set_bool

unsafe axiom options.set_nat : options → Name → Nat → options
#align options.set_nat options.set_nat

unsafe axiom options.set_string : options → Name → String → options
#align options.set_string options.set_string

unsafe axiom options.get_bool : options → Name → Bool → Bool
#align options.get_bool options.get_bool

unsafe axiom options.get_nat : options → Name → Nat → Nat
#align options.get_nat options.get_nat

unsafe axiom options.get_string : options → Name → String → String
#align options.get_string options.get_string

unsafe axiom options.join : options → options → options
#align options.join options.join

unsafe axiom options.fold {α : Type u} : options → α → (Name → α → α) → α
#align options.fold options.fold

unsafe axiom options.has_decidable_eq : DecidableEq options
#align options.has_decidable_eq options.has_decidable_eq

attribute [instance] options.has_decidable_eq

unsafe instance : Add options :=
  ⟨options.join⟩

unsafe instance : Inhabited options :=
  ⟨options.mk⟩

