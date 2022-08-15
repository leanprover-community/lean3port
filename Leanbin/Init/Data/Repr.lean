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
class HasRepr (α : Type u) where
  repr : α → Stringₓ

/--
`repr` is similar to `to_string` except that we should have the property `eval (repr x) = x` for most sensible datatypes.
Hence, `repr "hello"` has the value `"\"hello\""` not `"hello"`.  -/
def reprₓ {α : Type u} [HasRepr α] : α → Stringₓ :=
  HasRepr.repr

instance : HasRepr Bool :=
  ⟨fun b => cond b "tt" "ff"⟩

instance {p : Prop} : HasRepr (Decidable p) :=
  ⟨-- Remark: type class inference will not consider local instance `b` in the new elaborator
  fun b : Decidable p => @ite _ p b "tt" "ff"⟩

protected def List.reprAux {α : Type u} [HasRepr α] : Bool → List α → Stringₓ
  | b, [] => ""
  | tt, x :: xs => reprₓ x ++ List.reprAux false xs
  | ff, x :: xs => ", " ++ reprₓ x ++ List.reprAux false xs

protected def List.reprₓ {α : Type u} [HasRepr α] : List α → Stringₓ
  | [] => "[]"
  | x :: xs => "[" ++ List.reprAux true (x :: xs) ++ "]"

instance {α : Type u} [HasRepr α] : HasRepr (List α) :=
  ⟨List.reprₓ⟩

instance : HasRepr Unit :=
  ⟨fun u => "star"⟩

instance {α : Type u} [HasRepr α] : HasRepr (Option α) :=
  ⟨fun o =>
    match o with
    | none => "none"
    | some a => "(some " ++ reprₓ a ++ ")"⟩

instance {α : Type u} {β : Type v} [HasRepr α] [HasRepr β] : HasRepr (Sum α β) :=
  ⟨fun s =>
    match s with
    | inl a => "(inl " ++ reprₓ a ++ ")"
    | inr b => "(inr " ++ reprₓ b ++ ")"⟩

instance {α : Type u} {β : Type v} [HasRepr α] [HasRepr β] : HasRepr (α × β) :=
  ⟨fun ⟨a, b⟩ => "(" ++ reprₓ a ++ ", " ++ reprₓ b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [HasRepr α] [s : ∀ x, HasRepr (β x)] : HasRepr (Sigma β) :=
  ⟨fun ⟨a, b⟩ => "⟨" ++ reprₓ a ++ ", " ++ reprₓ b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [HasRepr α] : HasRepr (Subtype p) :=
  ⟨fun s => reprₓ (val s)⟩

namespace Nat

def digitCharₓ (n : ℕ) : Charₓ :=
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

def toDigitsₓ (base : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => digitSucc base (to_digits n)

protected def reprₓ (n : ℕ) : Stringₓ :=
  ((toDigitsₓ 10 n).map digitCharₓ).reverse.asString

end Nat

instance : HasRepr Nat :=
  ⟨Nat.reprₓ⟩

def hexDigitReprₓ (n : Nat) : Stringₓ :=
  Stringₓ.singleton <| Nat.digitCharₓ n

def charToHex (c : Charₓ) : Stringₓ :=
  let n := Charₓ.toNat c
  let d2 := n / 16
  let d1 := n % 16
  hexDigitReprₓ d2 ++ hexDigitReprₓ d1

def Charₓ.quoteCore (c : Charₓ) : Stringₓ :=
  if c = '\n' then "\\n"
  else
    if c = '\t' then "\\t"
    else
      if c = '\\' then "\\\\"
      else if c = '\"' then "\\\"" else if c.toNat ≤ 31 ∨ c = '\x7f' then "\\x" ++ charToHex c else Stringₓ.singleton c

instance : HasRepr Charₓ :=
  ⟨fun c => "'" ++ Charₓ.quoteCore c ++ "'"⟩

def Stringₓ.quoteAux : List Charₓ → Stringₓ
  | [] => ""
  | x :: xs => Charₓ.quoteCore x ++ Stringₓ.quoteAux xs

def Stringₓ.quote (s : Stringₓ) : Stringₓ :=
  if s.isEmpty = tt then "\"\"" else "\"" ++ Stringₓ.quoteAux s.toList ++ "\""

instance : HasRepr Stringₓ :=
  ⟨Stringₓ.quote⟩

instance (n : Nat) : HasRepr (Finₓ n) :=
  ⟨fun f => reprₓ f.val⟩

instance : HasRepr Unsigned :=
  ⟨fun n => reprₓ n.val⟩

def Charₓ.repr (c : Charₓ) : Stringₓ :=
  reprₓ c

