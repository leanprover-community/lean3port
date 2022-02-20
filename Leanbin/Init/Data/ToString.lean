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

open Sum Subtype Nat

universe u v

/-- Convert the object into a string for tracing/display purposes.
Similar to Haskell's `show`.
See also `has_repr`, which is used to output a string which is a valid lean code.
See also `has_to_format` and `has_to_tactic_format`, `format` has additional support for colours and pretty printing multilines.
 -/
class HasToString (α : Type u) where
  toString : α → Stringₓ

def toString {α : Type u} [HasToString α] : α → Stringₓ :=
  HasToString.toString

instance : HasToString Stringₓ :=
  ⟨fun s => s⟩

instance : HasToString Bool :=
  ⟨fun b => cond b "tt" "ff"⟩

instance {p : Prop} : HasToString (Decidable p) :=
  ⟨-- Remark: type class inference will not consider local instance `b` in the new elaborator
  fun b : Decidable p => @ite _ p b "tt" "ff"⟩

protected def List.toStringAuxₓ {α : Type u} [HasToString α] : Bool → List α → Stringₓ
  | b, [] => ""
  | tt, x :: xs => toString x ++ List.toStringAuxₓ false xs
  | ff, x :: xs => ", " ++ toString x ++ List.toStringAuxₓ false xs

protected def List.toStringₓ {α : Type u} [HasToString α] : List α → Stringₓ
  | [] => "[]"
  | x :: xs => "[" ++ List.toStringAuxₓ true (x :: xs) ++ "]"

instance {α : Type u} [HasToString α] : HasToString (List α) :=
  ⟨List.toStringₓ⟩

instance : HasToString Unit :=
  ⟨fun u => "star"⟩

instance : HasToString Nat :=
  ⟨fun n => reprₓ n⟩

instance : HasToString Charₓ :=
  ⟨fun c => c.toString⟩

instance (n : Nat) : HasToString (Finₓ n) :=
  ⟨fun f => toString f.val⟩

instance : HasToString Unsigned :=
  ⟨fun n => toString n.val⟩

instance {α : Type u} [HasToString α] : HasToString (Option α) :=
  ⟨fun o =>
    match o with
    | none => "none"
    | some a => "(some " ++ toString a ++ ")"⟩

instance {α : Type u} {β : Type v} [HasToString α] [HasToString β] : HasToString (Sum α β) :=
  ⟨fun s =>
    match s with
    | inl a => "(inl " ++ toString a ++ ")"
    | inr b => "(inr " ++ toString b ++ ")"⟩

instance {α : Type u} {β : Type v} [HasToString α] [HasToString β] : HasToString (α × β) :=
  ⟨fun ⟨a, b⟩ => "(" ++ toString a ++ ", " ++ toString b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [HasToString α] [s : ∀ x, HasToString (β x)] : HasToString (Sigma β) :=
  ⟨fun ⟨a, b⟩ => "⟨" ++ toString a ++ ", " ++ toString b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [HasToString α] : HasToString (Subtype p) :=
  ⟨fun s => toString (val s)⟩

