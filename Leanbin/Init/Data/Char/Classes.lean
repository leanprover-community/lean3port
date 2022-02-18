prelude
import Leanbin.Init.Data.Char.Basic
import Leanbin.Init.Data.Char.Lemmas
import Leanbin.Init.Meta.Default
import Leanbin.Init.Data.Int.Default

namespace Charₓ

def is_whitespace (c : Charₓ) : Prop :=
  c ∈ [' ', '\t', '\n']

def is_upper (c : Charₓ) : Prop :=
  c.val ≥ 65 ∧ c.val ≤ 90

def is_lower (c : Charₓ) : Prop :=
  c.val ≥ 97 ∧ c.val ≤ 122

def is_alpha (c : Charₓ) : Prop :=
  c.IsUpper ∨ c.IsLower

def is_digit (c : Charₓ) : Prop :=
  c.val ≥ 48 ∧ c.val ≤ 57

def is_alphanum (c : Charₓ) : Prop :=
  c.IsAlpha ∨ c.IsDigit

def is_punctuation (c : Charₓ) : Prop :=
  c ∈ [' ', ',', '.', '?', '!', ';', '-', ''']

def to_lower (c : Charₓ) : Charₓ :=
  let n := toNat c
  if n ≥ 65 ∧ n ≤ 90 then ofNat (n + 32) else c

instance decidable_is_whitespace : DecidablePred IsWhitespace := by
  intro c
  delta' is_whitespace
  infer_instance

instance decidable_is_upper : DecidablePred IsUpper := by
  intro c
  delta' is_upper
  infer_instance

instance decidable_is_lower : DecidablePred IsLower := by
  intro c
  delta' is_lower
  infer_instance

instance decidable_is_alpha : DecidablePred IsAlpha := by
  intro c
  delta' is_alpha
  infer_instance

instance decidable_is_digit : DecidablePred IsDigit := by
  intro c
  delta' is_digit
  infer_instance

instance decidable_is_alphanum : DecidablePred IsAlphanum := by
  intro c
  delta' is_alphanum
  infer_instance

instance decidable_is_punctuation : DecidablePred IsPunctuation := by
  intro c
  delta' is_punctuation
  infer_instance

end Charₓ

