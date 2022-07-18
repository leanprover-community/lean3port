/-
Copyright (c) E.W.Ayers 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import Leanbin.Init.Data.Default
import Leanbin.Init.Meta.Float

unsafe inductive json : Type
  | of_string : Stringₓ → json
  | of_int : Int → json
  | of_float : native.float → json
  | of_bool : Bool → json
  | null : json
  | object : List (Stringₓ × json) → json
  | Arrayₓ : List json → json

namespace Json

unsafe instance string_coe : Coe Stringₓ json :=
  ⟨json.of_string⟩

unsafe instance int_coe : Coe Int json :=
  ⟨json.of_int⟩

unsafe instance float_coe : Coe native.float json :=
  ⟨json.of_float⟩

unsafe instance bool_coe : Coe Bool json :=
  ⟨json.of_bool⟩

unsafe instance array_coe : Coe (List json) json :=
  ⟨json.array⟩

unsafe instance : Inhabited json :=
  ⟨json.null⟩

protected unsafe axiom parse : Stringₓ → Option json

protected unsafe axiom unparse : json → Stringₓ

unsafe def to_format : json → format
  | of_string s => Stringₓ.quote s
  | of_int i => toString i
  | of_float f => toString f
  | of_bool tt => "true"
  | of_bool ff => "false"
  | null => "null"
  | object kvs =>
    "{ " ++
        (format.group <|
          format.nest 2 <|
            format.join <|
              List.intersperse (", " ++ format.line) <| kvs.map fun ⟨k, v⟩ => Stringₓ.quote k ++ ":" ++ to_format v) ++
      "}"
  | Arrayₓ js => list.to_format <| js.map to_format

unsafe instance : has_to_format json :=
  ⟨to_format⟩

unsafe instance : HasToString json :=
  ⟨json.unparse⟩

unsafe instance : HasRepr json :=
  ⟨json.unparse⟩

unsafe instance : DecidableEq json := fun j₁ j₂ => by
  cases j₁ <;>
    cases j₂ <;>
      simp <;>
        try
          apply Decidable.false
  -- do this explicitly casewise to be extra sure we don't recurse unintentionally, as meta code
  -- doesn't protect against this.
  case json.of_string =>
    exact Stringₓ.hasDecidableEq _ _
  case json.of_float =>
    exact native.float.dec_eq _ _
  case json.of_int =>
    exact Int.decidableEq _ _
  case json.of_bool =>
    exact Bool.decidableEq _ _
  case json.null =>
    exact Decidable.true
  case json.array =>
    let this := DecidableEq
    exact List.decidableEq _ _
  case json.object =>
    let this := DecidableEq
    exact List.decidableEq _ _

end Json

