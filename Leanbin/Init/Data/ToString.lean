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
import Leanbin.Init.Data.Repr

#align_import init.data.to_string from "leanprover-community/lean"@"c248e38671ebca7d0513180887daf60a6433bc37"

open Sum Subtype Nat

universe u v

#print ToString /-
/-- Convert the object into a string for tracing/display purposes.
Similar to Haskell's `show`.
See also `has_repr`, which is used to output a string which is a valid lean code.
See also `has_to_format` and `has_to_tactic_format`, `format` has additional support for colours and pretty printing multilines.
 -/
class ToString (α : Type u) where
  toString : α → String
#align has_to_string ToString
-/

def toString {α : Type u} [ToString α] : α → String :=
  ToString.toString
#align to_string toString

instance : ToString String :=
  ⟨fun s => s⟩

instance : ToString Bool :=
  ⟨fun b => cond b "tt" "ff"⟩

instance {p : Prop} : ToString (Decidable p) :=
  ⟨-- Remark: type class inference will not consider local instance `b` in the new elaborator
  fun b : Decidable p => @ite _ p b "tt" "ff"⟩

protected def List.toStringAux {α : Type u} [ToString α] : Bool → List α → String
  | b, [] => ""
  | tt, x :: xs => toString x ++ List.toStringAux false xs
  | ff, x :: xs => ", " ++ toString x ++ List.toStringAux false xs
#align list.to_string_aux List.toStringAux

#print List.toString /-
protected def List.toString {α : Type u} [ToString α] : List α → String
  | [] => "[]"
  | x :: xs => "[" ++ List.toStringAux true (x :: xs) ++ "]"
#align list.to_string List.toString
-/

instance {α : Type u} [ToString α] : ToString (List α) :=
  ⟨List.toString⟩

instance : ToString Unit :=
  ⟨fun u => "star"⟩

instance : ToString Nat :=
  ⟨fun n => repr n⟩

instance : ToString Char :=
  ⟨fun c => c.toString⟩

instance (n : Nat) : ToString (Fin n) :=
  ⟨fun f => toString f.val⟩

instance : ToString Unsigned :=
  ⟨fun n => toString n.val⟩

instance {α : Type u} [ToString α] : ToString (Option α) :=
  ⟨fun o =>
    match o with
    | none => "none"
    | some a => "(some " ++ toString a ++ ")"⟩

instance {α : Type u} {β : Type v} [ToString α] [ToString β] : ToString (Sum α β) :=
  ⟨fun s =>
    match s with
    | inl a => "(inl " ++ toString a ++ ")"
    | inr b => "(inr " ++ toString b ++ ")"⟩

instance {α : Type u} {β : Type v} [ToString α] [ToString β] : ToString (α × β) :=
  ⟨fun ⟨a, b⟩ => "(" ++ toString a ++ ", " ++ toString b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [ToString α] [s : ∀ x, ToString (β x)] :
    ToString (Sigma β) :=
  ⟨fun ⟨a, b⟩ => "⟨" ++ toString a ++ ", " ++ toString b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [ToString α] : ToString (Subtype p) :=
  ⟨fun s => toString (val s)⟩

