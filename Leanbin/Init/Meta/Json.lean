/-
Copyright (c) E.W.Ayers 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import Leanbin.Init.Data.Default
import Leanbin.Init.Meta.Float

unsafe inductive json : Type
  | of_string : String → json
  | of_int : Int → json
  | of_float : native.float → json
  | of_bool : Bool → json
  | null : json
  | object : List (String × json) → json
  | Array' : List json → json
#align json json

namespace Json

unsafe instance string_coe : Coe String json :=
  ⟨json.of_string⟩
#align json.string_coe json.string_coe

unsafe instance int_coe : Coe Int json :=
  ⟨json.of_int⟩
#align json.int_coe json.int_coe

unsafe instance float_coe : Coe native.float json :=
  ⟨json.of_float⟩
#align json.float_coe json.float_coe

unsafe instance bool_coe : Coe Bool json :=
  ⟨json.of_bool⟩
#align json.bool_coe json.bool_coe

unsafe instance array_coe : Coe (List json) json :=
  ⟨json.array⟩
#align json.array_coe json.array_coe

unsafe instance : Inhabited json :=
  ⟨json.null⟩

protected unsafe axiom parse : String → Option json
#align json.parse json.parse

protected unsafe axiom unparse : json → String
#align json.unparse json.unparse

unsafe def to_format : json → format
  | of_string s => String.quote s
  | of_int i => toString i
  | of_float f => toString f
  | of_bool tt => "true"
  | of_bool ff => "false"
  | null => "null"
  | object kvs =>
    "{ " ++
        (format.group $
          format.nest 2 $
            format.join $
              List.intersperse (", " ++ format.line) $ kvs.map $ fun ⟨k, v⟩ => String.quote k ++ ":" ++ to_format v) ++
      "}"
  | Array' js => list.to_format $ js.map to_format
#align json.to_format json.to_format

unsafe instance : has_to_format json :=
  ⟨to_format⟩

unsafe instance : ToString json :=
  ⟨json.unparse⟩

unsafe instance : Repr json :=
  ⟨json.unparse⟩

unsafe instance : DecidableEq json := fun j₁ j₂ => by
  cases j₁ <;> cases j₂ <;> simp <;> try apply Decidable.false
  -- do this explicitly casewise to be extra sure we don't recurse unintentionally, as meta code
  -- doesn't protect against this.
  case of_string => exact String.hasDecidableEq _ _
  case of_float => exact native.float.dec_eq _ _
  case of_int => exact Int.decidableEq _ _
  case of_bool => exact Bool.decidableEq _ _
  case null => exact Decidable.true
  case array =>
  letI := DecidableEq
  exact List.decidableEq _ _
  case object =>
  letI := DecidableEq
  exact List.decidableEq _ _

end Json

