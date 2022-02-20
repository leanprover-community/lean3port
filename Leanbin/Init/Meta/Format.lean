/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Options
import Leanbin.Init.Function
import Leanbin.Init.Data.ToString

universe u v

inductive Format.Color
  | red
  | green
  | orange
  | blue
  | pink
  | cyan
  | grey

def Format.Color.toString : Format.Color → Stringₓ
  | Format.Color.red => "red"
  | Format.Color.green => "green"
  | Format.Color.orange => "orange"
  | Format.Color.blue => "blue"
  | Format.Color.pink => "pink"
  | Format.Color.cyan => "cyan"
  | Format.Color.grey => "grey"

/--
Format is a rich string with highlighting and information about how tabs should be put in if linebreaks are needed. A 'pretty string'. -/
unsafe axiom format : Type

/-- Indicate that it is ok to put a linebreak in here if the line is too long. -/
unsafe axiom format.line : format

/-- The whitespace character `" "`. -/
unsafe axiom format.space : format

/-- = `""` -/
unsafe axiom format.nil : format

/-- Concatenate the given format strings. -/
unsafe axiom format.compose : format → format → format

/-- `format.nest n f` tells the formatter that `f` is nested inside something with length `n`
so that it is pretty-printed with the correct tabs on a line break.
For example, in `list.to_format` we have:

```
(nest 1 $ format.join $ list.intersperse ("," ++ line) $ xs.map to_fmt)
```

This will be written all on one line, but when the list is too large, it will put in linebreaks after the comma and indent later lines by 1.
 -/
unsafe axiom format.nest : Nat → format → format

/-- Make the given format be displayed a particular color. -/
unsafe axiom format.highlight : format → Color → format

/--
When printing the given format `f`, if `f.flatten` fits without need for linebreaks then print the `f.flatten`, else print `f` unflattened with linebreaks. -/
unsafe axiom format.group : format → format

unsafe axiom format.of_string : Stringₓ → format

unsafe axiom format.of_nat : Nat → format

/-- Flattening removes all of the `format.nest` items from the format tree.  -/
unsafe axiom format.flatten : format → format

unsafe axiom format.to_string (f : format) (o : options := options.mk) : Stringₓ

unsafe axiom format.of_options : options → format

unsafe axiom format.is_nil : format → Bool

/-- Traces the given format to the output window, then performs the given continuation.  -/
unsafe axiom trace_fmt {α : Type u} : format → (Unit → α) → α

unsafe instance : Inhabited format :=
  ⟨format.space⟩

unsafe instance : Append format :=
  ⟨format.compose⟩

unsafe instance : HasToString format :=
  ⟨fun f => f.toString options.mk⟩

/-- Use this instead of `has_to_string` to enable prettier formatting.
See docstring for `format` for more on the differences between `format` and `string`.
Note that `format` is `meta` while `string` is not. -/
unsafe class has_to_format (α : Type u) where
  to_format : α → format

unsafe instance : has_to_format format :=
  ⟨id⟩

unsafe def to_fmt {α : Type u} [has_to_format α] : α → format :=
  has_to_format.to_format

unsafe instance nat_to_format : Coe Nat format :=
  ⟨format.of_nat⟩

unsafe instance string_to_format : Coe Stringₓ format :=
  ⟨format.of_string⟩

open Format List

unsafe def format.indent (f : format) (n : Nat) : format :=
  nest n (line ++ f)

unsafe def format.when {α : Type u} [has_to_format α] : Bool → α → format
  | tt, a => to_fmt a
  | ff, a => nil

unsafe def format.join (xs : List format) : format :=
  foldlₓ compose (of_string "") xs

unsafe instance : has_to_format options :=
  ⟨fun o => format.of_options o⟩

unsafe instance : has_to_format Bool :=
  ⟨fun b => if b then of_string "tt" else of_string "ff"⟩

unsafe instance {p : Prop} : has_to_format (Decidable p) :=
  ⟨fun b : Decidable p => @ite _ p b (of_string "tt") (of_string "ff")⟩

unsafe instance : has_to_format Stringₓ :=
  ⟨fun s => format.of_string s⟩

unsafe instance : has_to_format Nat :=
  ⟨fun n => format.of_nat n⟩

unsafe instance : has_to_format Unsigned :=
  ⟨fun n => to_fmt n.toNat⟩

unsafe instance : has_to_format Charₓ :=
  ⟨fun c : Charₓ => format.of_string c.toString⟩

unsafe def list.to_format {α : Type u} [has_to_format α] : List α → format
  | [] => to_fmt "[]"
  | xs => to_fmt "[" ++ group (nest 1 <| format.join <| List.intersperse ("," ++ line) <| xs.map to_fmt) ++ to_fmt "]"

unsafe instance {α : Type u} [has_to_format α] : has_to_format (List α) :=
  ⟨list.to_format⟩

attribute [instance] string.has_to_format

unsafe instance : has_to_format Name :=
  ⟨fun n => to_fmt n.toString⟩

unsafe instance : has_to_format Unit :=
  ⟨fun u => to_fmt "()"⟩

unsafe instance {α : Type u} [has_to_format α] : has_to_format (Option α) :=
  ⟨fun o => Option.casesOn o (to_fmt "none") fun a => to_fmt "(some " ++ nest 6 (to_fmt a) ++ to_fmt ")"⟩

unsafe instance sum_has_to_format {α : Type u} {β : Type v} [has_to_format α] [has_to_format β] :
    has_to_format (Sum α β) :=
  ⟨fun s =>
    Sum.casesOn s (fun a => to_fmt "(inl " ++ nest 5 (to_fmt a) ++ to_fmt ")") fun b =>
      to_fmt "(inr " ++ nest 5 (to_fmt b) ++ to_fmt ")"⟩

open Prod

unsafe instance {α : Type u} {β : Type v} [has_to_format α] [has_to_format β] : has_to_format (Prod α β) :=
  ⟨fun ⟨a, b⟩ => group (nest 1 (to_fmt "(" ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt ")"))⟩

open Sigma

unsafe instance {α : Type u} {β : α → Type v} [has_to_format α] [s : ∀ x, has_to_format (β x)] :
    has_to_format (Sigma β) :=
  ⟨fun ⟨a, b⟩ => group (nest 1 (to_fmt "⟨" ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt "⟩"))⟩

open Subtype

unsafe instance {α : Type u} {p : α → Prop} [has_to_format α] : has_to_format (Subtype p) :=
  ⟨fun s => to_fmt (val s)⟩

unsafe def format.bracket : Stringₓ → Stringₓ → format → format
  | o, c, f => to_fmt o ++ nest o.length f ++ to_fmt c

/-- Surround with "()". -/
unsafe def format.paren (f : format) : format :=
  format.bracket "(" ")" f

/-- Surround with "{}". -/
unsafe def format.cbrace (f : format) : format :=
  format.bracket "{" "}" f

/-- Surround with "[]". -/
unsafe def format.sbracket (f : format) : format :=
  format.bracket "[" "]" f

/-- Surround with "⦃⦄". -/
unsafe def format.dcbrace (f : format) : format :=
  to_fmt "⦃" ++ nest 1 f ++ to_fmt "⦄"

