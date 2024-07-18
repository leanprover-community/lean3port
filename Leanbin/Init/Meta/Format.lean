/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta.Options
import Logic.Function.Defs
import Init.Data.ToString

#align_import init.meta.format from "leanprover-community/lean"@"c248e38671ebca7d0513180887daf60a6433bc37"

universe u v

inductive Format.Color
  | red
  | green
  | orange
  | blue
  | pink
  | cyan
  | grey
#align format.color Format.Color

def Format.Color.toString : Format.Color → String
  | Format.Color.red => "red"
  | Format.Color.green => "green"
  | Format.Color.orange => "orange"
  | Format.Color.blue => "blue"
  | Format.Color.pink => "pink"
  | Format.Color.cyan => "cyan"
  | Format.Color.grey => "grey"
#align format.color.to_string Format.Color.toString

/--
Format is a rich string with highlighting and information about how tabs should be put in if linebreaks are needed. A 'pretty string'. -/
unsafe axiom format : Type
#align format format

/-- Indicate that it is ok to put a linebreak in here if the line is too long. -/
unsafe axiom format.line : format
#align format.line format.line

/-- The whitespace character `" "`. -/
unsafe axiom format.space : format
#align format.space format.space

/-- = `""` -/
unsafe axiom format.nil : format
#align format.nil format.nil

/-- Concatenate the given format strings. -/
unsafe axiom format.compose : format → format → format
#align format.compose format.compose

/-- `format.nest n f` tells the formatter that `f` is nested inside something with length `n`
so that it is pretty-printed with the correct tabs on a line break.
For example, in `list.to_format` we have:

```
(nest 1 $ format.join $ list.intersperse ("," ++ line) $ xs.map to_fmt)
```

This will be written all on one line, but when the list is too large, it will put in linebreaks after the comma and indent later lines by 1.
 -/
unsafe axiom format.nest : Nat → format → format
#align format.nest format.nest

/-- Make the given format be displayed a particular color. -/
unsafe axiom format.highlight : format → Color → format
#align format.highlight format.highlight

/--
When printing the given format `f`, if `f.flatten` fits without need for linebreaks then print the `f.flatten`, else print `f` unflattened with linebreaks. -/
unsafe axiom format.group : format → format
#align format.group format.group

unsafe axiom format.of_string : String → format
#align format.of_string format.of_string

unsafe axiom format.of_nat : Nat → format
#align format.of_nat format.of_nat

/-- Flattening removes all of the `format.nest` items from the format tree.  -/
unsafe axiom format.flatten : format → format
#align format.flatten format.flatten

unsafe axiom format.to_string (f : format) (o : options := options.mk) : String
#align format.to_string format.to_string

unsafe axiom format.of_options : options → format
#align format.of_options format.of_options

unsafe axiom format.is_nil : format → Bool
#align format.is_nil format.is_nil

/-- Traces the given format to the output window, then performs the given continuation.  -/
unsafe axiom trace_fmt {α : Type u} : format → (Unit → α) → α
#align trace_fmt trace_fmt

unsafe instance : Inhabited format :=
  ⟨format.space⟩

unsafe instance : Append format :=
  ⟨format.compose⟩

unsafe instance : ToString format :=
  ⟨fun f => f.toString options.mk⟩

/-- Use this instead of `has_to_string` to enable prettier formatting.
See docstring for `format` for more on the differences between `format` and `string`.
Note that `format` is `meta` while `string` is not. -/
unsafe class has_to_format (α : Type u) where
  to_format : α → format
#align has_to_format has_to_format

unsafe instance : has_to_format format :=
  ⟨id⟩

unsafe def to_fmt {α : Type u} [has_to_format α] : α → format :=
  has_to_format.to_format
#align to_fmt to_fmt

unsafe instance nat_to_format : Coe Nat format :=
  ⟨format.of_nat⟩
#align nat_to_format nat_to_format

unsafe instance string_to_format : Coe String format :=
  ⟨format.of_string⟩
#align string_to_format string_to_format

open Format List

unsafe def format.indent (f : format) (n : Nat) : format :=
  nest n (line ++ f)
#align format.indent format.indent

unsafe def format.when {α : Type u} [has_to_format α] : Bool → α → format
  | tt, a => to_fmt a
  | ff, a => nil
#align format.when format.when

unsafe def format.join (xs : List format) : format :=
  foldl compose (of_string "") xs
#align format.join format.join

unsafe instance : has_to_format options :=
  ⟨fun o => format.of_options o⟩

unsafe instance : has_to_format Bool :=
  ⟨fun b => if b then of_string "tt" else of_string "ff"⟩

unsafe instance {p : Prop} : has_to_format (Decidable p) :=
  ⟨fun b : Decidable p => @ite _ p b (of_string "tt") (of_string "ff")⟩

unsafe instance : has_to_format String :=
  ⟨fun s => format.of_string s⟩

unsafe instance : has_to_format Nat :=
  ⟨fun n => format.of_nat n⟩

unsafe instance : has_to_format Unsigned :=
  ⟨fun n => to_fmt n.toNat⟩

unsafe instance : has_to_format Char :=
  ⟨fun c : Char => format.of_string c.toString⟩

unsafe def list.to_format {α : Type u} [has_to_format α] : List α → format
  | [] => to_fmt "[]"
  | xs =>
    to_fmt "[" ++
        group (nest 1 <| format.join <| List.intersperse ("," ++ line) <| xs.map to_fmt) ++
      to_fmt "]"
#align list.to_format list.to_format

unsafe instance {α : Type u} [has_to_format α] : has_to_format (List α) :=
  ⟨list.to_format⟩

attribute [instance] string.has_to_format

unsafe instance : has_to_format Name :=
  ⟨fun n => to_fmt n.toString⟩

unsafe instance : has_to_format Unit :=
  ⟨fun u => to_fmt "()"⟩

unsafe instance {α : Type u} [has_to_format α] : has_to_format (Option α) :=
  ⟨fun o =>
    Option.casesOn o (to_fmt "none") fun a => to_fmt "(some " ++ nest 6 (to_fmt a) ++ to_fmt ")"⟩

unsafe instance sum_has_to_format {α : Type u} {β : Type v} [has_to_format α] [has_to_format β] :
    has_to_format (Sum α β) :=
  ⟨fun s =>
    Sum.casesOn s (fun a => to_fmt "(inl " ++ nest 5 (to_fmt a) ++ to_fmt ")") fun b =>
      to_fmt "(inr " ++ nest 5 (to_fmt b) ++ to_fmt ")"⟩
#align sum_has_to_format sum_has_to_format

open Prod

unsafe instance {α : Type u} {β : Type v} [has_to_format α] [has_to_format β] :
    has_to_format (Prod α β) :=
  ⟨fun ⟨a, b⟩ =>
    group (nest 1 (to_fmt "(" ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt ")"))⟩

open Sigma

unsafe instance {α : Type u} {β : α → Type v} [has_to_format α] [s : ∀ x, has_to_format (β x)] :
    has_to_format (Sigma β) :=
  ⟨fun ⟨a, b⟩ =>
    group (nest 1 (to_fmt "⟨" ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt "⟩"))⟩

open Subtype

unsafe instance {α : Type u} {p : α → Prop} [has_to_format α] : has_to_format (Subtype p) :=
  ⟨fun s => to_fmt (val s)⟩

unsafe def format.bracket : String → String → format → format
  | o, c, f => to_fmt o ++ nest o.length f ++ to_fmt c
#align format.bracket format.bracket

/-- Surround with "()". -/
unsafe def format.paren (f : format) : format :=
  format.bracket "(" ")" f
#align format.paren format.paren

/-- Surround with "{}". -/
unsafe def format.cbrace (f : format) : format :=
  format.bracket "{" "}" f
#align format.cbrace format.cbrace

/-- Surround with "[]". -/
unsafe def format.sbracket (f : format) : format :=
  format.bracket "[" "]" f
#align format.sbracket format.sbracket

/-- Surround with "⦃⦄". -/
unsafe def format.dcbrace (f : format) : format :=
  to_fmt "⦃" ++ nest 1 f ++ to_fmt "⦄"
#align format.dcbrace format.dcbrace

