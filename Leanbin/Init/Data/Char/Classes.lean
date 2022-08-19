/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
prelude
import Leanbin.Init.Data.Char.Basic
import Leanbin.Init.Data.Char.Lemmas
import Leanbin.Init.Meta.Default
import Leanbin.Init.Data.Int.Default

namespace Char

def IsWhitespace (c : Char) : Prop :=
  c ∈ [' ', '\t', '\n']

def IsUpper (c : Char) : Prop :=
  c.val ≥ 65 ∧ c.val ≤ 90

def IsLower (c : Char) : Prop :=
  c.val ≥ 97 ∧ c.val ≤ 122

def IsAlpha (c : Char) : Prop :=
  c.IsUpper ∨ c.IsLower

def IsDigit (c : Char) : Prop :=
  c.val ≥ 48 ∧ c.val ≤ 57

def IsAlphanum (c : Char) : Prop :=
  c.IsAlpha ∨ c.IsDigit

def IsPunctuation (c : Char) : Prop :=
  c ∈ [' ', ',', '.', '?', '!', ';', '-', ''']

instance decidableIsWhitespace : DecidablePred IsWhitespace := by
  intro c
  delta IsWhitespace
  infer_instance

instance decidableIsUpper : DecidablePred IsUpper := by
  intro c
  delta IsUpper
  infer_instance

instance decidableIsLower : DecidablePred IsLower := by
  intro c
  delta IsLower
  infer_instance

instance decidableIsAlpha : DecidablePred IsAlpha := by
  intro c
  delta IsAlpha
  infer_instance

instance decidableIsDigit : DecidablePred IsDigit := by
  intro c
  delta IsDigit
  infer_instance

instance decidableIsAlphanum : DecidablePred IsAlphanum := by
  intro c
  delta IsAlphanum
  infer_instance

instance decidableIsPunctuation : DecidablePred IsPunctuation := by
  intro c
  delta IsPunctuation
  infer_instance

end Char

