/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.String.Basic
import Leanbin.Init.Data.Bool.Basic
import Leanbin.Init.Data.Subtype.Basic
import Leanbin.Init.Data.Unsigned.Basic
import Leanbin.Init.Data.Prod
import Leanbin.Init.Data.Sum.Basic
import Leanbin.Init.Data.Nat.Div

open Sum Subtype Nat

universe u v

/-- Implement `has_repr` if the output string is valid lean code that evaluates back to the original object.
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

/- warning: repr -> repr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Repr.{u} α], α -> String
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Init.Data.Repr._hyg.17 : Repr.{u_1} α], α -> Std.Format
Case conversion may be inaccurate. Consider using '#align repr reprₓ'. -/
/--
`repr` is similar to `to_string` except that we should have the property `eval (repr x) = x` for most sensible datatypes.
Hence, `repr "hello"` has the value `"\"hello\""` not `"hello"`.  -/
def repr {α : Type u} [Repr α] : α → String :=
  Repr.repr

instance : Repr Bool :=
  ⟨fun b => cond b "tt" "ff"⟩

instance {p : Prop} : Repr (Decidable p) :=
  ⟨-- Remark: type class inference will not consider local instance `b` in the new elaborator
  fun b : Decidable p => @ite _ p b "tt" "ff"⟩

protected def List.reprAux {α : Type u} [Repr α] : Bool → List α → String
  | b, [] => ""
  | tt, x :: xs => repr x ++ List.reprAux false xs
  | ff, x :: xs => ", " ++ repr x ++ List.reprAux false xs

/- warning: list.repr -> List.repr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Repr.{u} α], (List.{u} α) -> String
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Init.Data.Repr._hyg.2104 : Repr.{u_1} α], (List.{u_1} α) -> Nat -> Std.Format
Case conversion may be inaccurate. Consider using '#align list.repr List.reprₓ'. -/
protected def List.repr {α : Type u} [Repr α] : List α → String
  | [] => "[]"
  | x :: xs => "[" ++ List.reprAux true (x :: xs) ++ "]"

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
                          else if n = 13 then 'd' else if n = 14 then 'e' else if n = 15 then 'f' else '*'

def digitSucc (base : ℕ) : List ℕ → List ℕ
  | [] => [1]
  | d :: ds => if d + 1 = base then 0 :: digit_succ ds else (d + 1) :: ds

def toDigits' (base : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => digitSucc base (to_digits n)

protected def repr (n : ℕ) : String :=
  ((toDigits' 10 n).map digitChar).reverse.asString

end Nat

instance : Repr Nat :=
  ⟨Nat.repr⟩

def hexDigitRepr (n : Nat) : String :=
  String.singleton <| Nat.digitChar n

def charToHex (c : Char) : String :=
  let n := Char.toNat c
  let d2 := n / 16
  let d1 := n % 16
  hexDigitRepr d2 ++ hexDigitRepr d1

def Char.quoteCore (c : Char) : String :=
  if c = '\n' then "\\n"
  else
    if c = '\t' then "\\t"
    else
      if c = '\\' then "\\\\"
      else if c = '\"' then "\\\"" else if c.toNat ≤ 31 ∨ c = '\x7f' then "\\x" ++ charToHex c else String.singleton c

instance : Repr Char :=
  ⟨fun c => "'" ++ Char.quoteCore c ++ "'"⟩

def String.quoteAux : List Char → String
  | [] => ""
  | x :: xs => Char.quoteCore x ++ String.quoteAux xs

def String.quote (s : String) : String :=
  if s.isEmpty = tt then "\"\"" else "\"" ++ String.quoteAux s.toList ++ "\""

instance : Repr String :=
  ⟨String.quote⟩

instance (n : Nat) : Repr (Fin n) :=
  ⟨fun f => repr f.val⟩

instance : Repr Unsigned :=
  ⟨fun n => repr n.val⟩

def Char.repr (c : Char) : String :=
  repr c

