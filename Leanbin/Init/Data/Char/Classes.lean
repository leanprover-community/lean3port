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
#align char.is_whitespace Char.IsWhitespace

def IsUpper (c : Char) : Prop :=
  c.val ≥ 65 ∧ c.val ≤ 90
#align char.is_upper Char.IsUpper

def IsLower (c : Char) : Prop :=
  c.val ≥ 97 ∧ c.val ≤ 122
#align char.is_lower Char.IsLower

def IsAlpha (c : Char) : Prop :=
  c.IsUpper ∨ c.IsLower
#align char.is_alpha Char.IsAlpha

def IsDigit (c : Char) : Prop :=
  c.val ≥ 48 ∧ c.val ≤ 57
#align char.is_digit Char.IsDigit

def IsAlphanum (c : Char) : Prop :=
  c.IsAlpha ∨ c.IsDigit
#align char.is_alphanum Char.IsAlphanum

def IsPunctuation (c : Char) : Prop :=
  c ∈ [' ', ',', '.', '?', '!', ';', '-', ''']
#align char.is_punctuation Char.IsPunctuation

#print Char.toLower /-
def toLower (c : Char) : Char :=
  let n := toNat c
  if n >= 65 ∧ n <= 90 then ofNat (n + 32) else c
#align char.to_lower Char.toLower
-/

instance decidableIsWhitespace : DecidablePred IsWhitespace := by
  intro c
  delta is_whitespace
  infer_instance
#align char.decidable_is_whitespace Char.decidableIsWhitespace

instance decidableIsUpper : DecidablePred IsUpper := by
  intro c
  delta is_upper
  infer_instance
#align char.decidable_is_upper Char.decidableIsUpper

instance decidableIsLower : DecidablePred IsLower := by
  intro c
  delta is_lower
  infer_instance
#align char.decidable_is_lower Char.decidableIsLower

instance decidableIsAlpha : DecidablePred IsAlpha := by
  intro c
  delta is_alpha
  infer_instance
#align char.decidable_is_alpha Char.decidableIsAlpha

instance decidableIsDigit : DecidablePred IsDigit := by
  intro c
  delta is_digit
  infer_instance
#align char.decidable_is_digit Char.decidableIsDigit

instance decidableIsAlphanum : DecidablePred IsAlphanum := by
  intro c
  delta is_alphanum
  infer_instance
#align char.decidable_is_alphanum Char.decidableIsAlphanum

instance decidableIsPunctuation : DecidablePred IsPunctuation := by
  intro c
  delta is_punctuation
  infer_instance
#align char.decidable_is_punctuation Char.decidableIsPunctuation

end Char

