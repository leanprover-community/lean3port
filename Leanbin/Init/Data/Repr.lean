/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Data.Bool.Basic
import Init.Data.Subtype.Basic
import Init.Data.Unsigned.Basic
import Init.Data.Prod
import Init.Data.Sum.Basic
import Init.Data.Nat.Div

#align_import init.data.repr from "leanprover-community/lean"@"c248e38671ebca7d0513180887daf60a6433bc37"

open Sum Subtype Nat

universe u v

#print Repr /-
/--
Implement `has_repr` if the output string is valid lean code that evaluates back to the original object.
If you just want to view the object as a string for a trace message, use `has_to_string`.

### Example:

```
#eval to_string "hello world"
-- [Lean] "hello world"
#eval repr "hello world"
-- [Lean] "\"hello world\""
```

Reference: https://github.com/leanprover/lean/issues/1664

 -/
class Repr (α : Type u) where
  repr : α → String
#align has_repr Repr
-/

#print repr /-
/--
`repr` is similar to `to_string` except that we should have the property `eval (repr x) = x` for most sensible datatypes.
Hence, `repr "hello"` has the value `"\"hello\""` not `"hello"`.  -/
def repr {α : Type u} [Repr α] : α → String :=
  Repr.repr
#align repr repr
-/

instance : Repr Bool :=
  ⟨fun b => cond b "tt" "ff"⟩

instance {p : Prop} : Repr (Decidable p) :=
  ⟨-- Remark: type class inference will not consider local instance `b` in the new elaborator
  fun b : Decidable p => @ite _ p b "tt" "ff"⟩

protected def List.reprAux {α : Type u} [Repr α] : Bool → List α → String
  | b, [] => ""
  | tt, x :: xs => repr x ++ List.reprAux false xs
  | ff, x :: xs => ", " ++ repr x ++ List.reprAux false xs
#align list.repr_aux List.reprAux

#print List.repr /-
protected def List.repr {α : Type u} [Repr α] : List α → String
  | [] => "[]"
  | x :: xs => "[" ++ List.reprAux true (x :: xs) ++ "]"
#align list.repr List.repr
-/

instance {α : Type u} [Repr α] : Repr (List α) :=
  ⟨List.repr⟩

instance : Repr Unit :=
  ⟨fun u => "star"⟩

instance {α : Type u} [Repr α] : Repr (Option α) :=
  ⟨fun o =>
    match o with
    | none => "none"
    | some a => "(some " ++ repr a ++ ")"⟩

instance {α : Type u} {β : Type v} [Repr α] [Repr β] : Repr (Sum α β) :=
  ⟨fun s =>
    match s with
    | inl a => "(inl " ++ repr a ++ ")"
    | inr b => "(inr " ++ repr b ++ ")"⟩

instance {α : Type u} {β : Type v} [Repr α] [Repr β] : Repr (α × β) :=
  ⟨fun ⟨a, b⟩ => "(" ++ repr a ++ ", " ++ repr b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [Repr α] [s : ∀ x, Repr (β x)] : Repr (Sigma β) :=
  ⟨fun ⟨a, b⟩ => "⟨" ++ repr a ++ ", " ++ repr b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [Repr α] : Repr (Subtype p) :=
  ⟨fun s => repr (val s)⟩

namespace Nat

#print Nat.digitChar /-
def digitChar (n : ℕ) : Char :=
  if n = 0 then '0'
  else
    if n = 1 then '1'
    else
      if n = 2 then '2'
      else
        if n = 3 then '3'
        else
          if n = 4 then '4'
          else
            if n = 5 then '5'
            else
              if n = 6 then '6'
              else
                if n = 7 then '7'
                else
                  if n = 8 then '8'
                  else
                    if n = 9 then '9'
                    else
                      if n = 10 then 'a'
                      else
                        if n = 11 then 'b'
                        else
                          if n = 12 then 'c'
                          else
                            if n = 13 then 'd'
                            else if n = 14 then 'e' else if n = 15 then 'f' else '*'
#align nat.digit_char Nat.digitChar
-/

def digitSucc (base : ℕ) : List ℕ → List ℕ
  | [] => [1]
  | d :: ds => if d + 1 = base then 0 :: digit_succ ds else (d + 1) :: ds
#align nat.digit_succ Nat.digitSucc

def toDigits' (base : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => digitSucc base (to_digits n)
#align nat.to_digits Nat.toDigits'

#print Nat.repr /-
protected def repr (n : ℕ) : String :=
  ((toDigits' 10 n).map digitChar).reverse.asString
#align nat.repr Nat.repr
-/

end Nat

instance : Repr Nat :=
  ⟨Nat.repr⟩

#print hexDigitRepr /-
def hexDigitRepr (n : Nat) : String :=
  String.singleton <| Nat.digitChar n
#align hex_digit_repr hexDigitRepr
-/

def charToHex (c : Char) : String :=
  let n := Char.toNat c
  let d2 := n / 16
  let d1 := n % 16
  hexDigitRepr d2 ++ hexDigitRepr d1
#align char_to_hex charToHex

#print Char.quoteCore /-
def Char.quoteCore (c : Char) : String :=
  if c = '\n' then "\\n"
  else
    if c = '\t' then "\\t"
    else
      if c = '\\' then "\\\\"
      else
        if c = '\"' then "\\\""
        else if c.toNat ≤ 31 ∨ c = '\x7f' then "\\x" ++ charToHex c else String.singleton c
#align char.quote_core Char.quoteCore
-/

instance : Repr Char :=
  ⟨fun c => "'" ++ Char.quoteCore c ++ "'"⟩

def String.quoteAux : List Char → String
  | [] => ""
  | x :: xs => Char.quoteCore x ++ String.quoteAux xs
#align string.quote_aux String.quoteAux

#print String.quote /-
def String.quote (s : String) : String :=
  if s.isEmpty = true then "\"\"" else "\"" ++ String.quoteAux s.toList ++ "\""
#align string.quote String.quote
-/

instance : Repr String :=
  ⟨String.quote⟩

instance (n : Nat) : Repr (Fin n) :=
  ⟨fun f => repr f.val⟩

instance : Repr Unsigned :=
  ⟨fun n => repr n.val⟩

#print Char.repr /-
def Char.repr (c : Char) : String :=
  repr c
#align char.repr Char.repr
-/

