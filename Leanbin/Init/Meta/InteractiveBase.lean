/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.Option.Basic
import Leanbin.Init.Meta.Lean.Parser
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.HasReflect

open Lean

open Lean.Parser

-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

-- mathport name: «expr *»
local postfix:1024 "*" => many

namespace Interactive

/-- (parse p) as the parameter type of an interactive tactic will instruct the Lean parser
    to run `p` when parsing the parameter and to pass the parsed value as an argument
    to the tactic. -/
@[reducible]
unsafe def parse {α : Type} (p : parser α) [lean.parser.reflectable p] : Type :=
  α

/--
A `loc` is either a 'wildcard', which means "everywhere", or a list of `option name`s. `none` means `target` and `some n` means `n` in the local context.-/
inductive Loc : Type
  | wildcard : loc
  | ns : List (Option Name) → loc

unsafe def loc.include_goal : Loc → Bool
  | loc.wildcard => true
  | loc.ns ls => (ls.map Option.isNone).bor

unsafe def loc.get_locals : Loc → tactic (List expr)
  | loc.wildcard => tactic.local_context
  | loc.ns xs =>
    xs.mfoldl
      (fun ls n =>
        match n with
        | none => pure ls
        | some n => do
          let l ← tactic.get_local n
          pure <| l :: ls)
      []

unsafe def loc.apply (hyp_tac : expr → tactic Unit) (goal_tac : tactic Unit) (l : Loc) : tactic Unit := do
  let hs ← l.get_locals
  hs hyp_tac
  if l then goal_tac else pure ()

unsafe def loc.try_apply (hyp_tac : expr → tactic Unit) (goal_tac : tactic Unit) (l : Loc) : tactic Unit := do
  let hs ← l.get_locals
  let hts := hs.map hyp_tac
  tactic.try_lst <| if l then hts ++ [goal_tac] else hts

/-- Use `desc` as the interactive description of `p`. -/
unsafe def with_desc {α : Type} (desc : format) (p : parser α) : parser α :=
  p

unsafe instance with_desc.reflectable {α : Type} (p : parser α) [h : lean.parser.reflectable p] (f : format) :
    reflectable (with_desc f p) :=
  h

namespace Types

variable {α β : Type}

-- optimized pretty printer
unsafe def brackets (l r : Stringₓ) (p : parser α) :=
  tk l *> p <* tk r

unsafe def list_of (p : parser α) :=
  brackets "[" "]" <| sep_by (skip_info (tk ",")) p

-- ./././Mathport/Syntax/Translate/Command.lean:619:29: warning: unsupported: precedence command
-- ./././Mathport/Syntax/Translate/Command.lean:619:29: warning: unsupported: precedence command
/-- The right-binding power 2 will terminate expressions by
    '<|>' (rbp 2), ';' (rbp 1), and ',' (rbp 0). It should be used for any (potentially)
    trailing expression parameters. -/
unsafe def tac_rbp :=
  2

/-- A 'tactic expression', which uses right-binding power 2 so that it is terminated by
    '<|>' (rbp 2), ';' (rbp 1), and ',' (rbp 0). It should be used for any (potentially)
    trailing expression parameters. -/
unsafe def texpr :=
  parser.pexpr tac_rbp

/-- Parse an identifier or a '_' -/
unsafe def ident_ : parser Name :=
  ident <|> tk "_" *> return `_

unsafe def using_ident :=
  (tk "using" *> ident)?

unsafe def with_ident_list :=
  tk "with" *> ident_* <|> return []

unsafe def without_ident_list :=
  tk "without" *> ident* <|> return []

unsafe def location :=
  tk "at" *>
      (tk "*" *> return Loc.wildcard <|>
        loc.ns <$> ((with_desc "⊢" <| tk "⊢" <|> tk "|-") *> return none <|> some <$> ident)*) <|>
    return (Loc.ns [none])

unsafe def pexpr_list :=
  list_of (parser.pexpr 0)

unsafe def opt_pexpr_list :=
  pexpr_list <|> return []

unsafe def pexpr_list_or_texpr :=
  pexpr_list <|> List.ret <$> texpr

unsafe def only_flag : parser Bool :=
  tk "only" *> return true <|> return false

end Types

-- ./././Mathport/Syntax/Translate/Command.lean:619:29: warning: unsupported: precedence command
open Expr Format Tactic Types

private unsafe def maybe_paren : List format → format
  | [] => ""
  | [f] => f
  | fs => paren (join fs)

private unsafe def unfold (e : expr) : tactic expr := do
  let expr.const f_name f_lvls ← return e.get_app_fn | failed
  let env ← get_env
  let decl ← env.get f_name
  let new_f ← decl.instantiate_value_univ_params f_lvls
  head_beta (expr.mk_app new_f e)

private unsafe def concat (f₁ f₂ : List format) :=
  if f₁.Empty then f₂ else if f₂.Empty then f₁ else f₁ ++ [" "] ++ f₂

private unsafe def parser_desc_aux : expr → tactic (List format)
  | quote.1 ident => return ["id"]
  | quote.1 ident_ => return ["id"]
  | quote.1 (parser.pexpr (%%ₓv)) => return ["expr"]
  | quote.1 small_nat => return ["n"]
  | quote.1 (tk (%%ₓc)) => List.ret <$> to_fmt <$> eval_expr Stringₓ c
  | quote.1 cur_pos => return []
  | quote.1 (pure _) => return []
  | quote.1 (_ <$> %%ₓp) => parser_desc_aux p
  | quote.1 (skip_info (%%ₓp)) => parser_desc_aux p
  | quote.1 (_ <$ %%ₓp) => parser_desc_aux p
  | quote.1 (set_goal_info_pos (%%ₓp)) => parser_desc_aux p
  | quote.1 (with_desc (%%ₓdesc) (%%ₓp)) => List.ret <$> eval_expr format desc
  | quote.1 ((%%ₓp₁) <*> %%ₓp₂) => do
    let f₁ ← parser_desc_aux p₁
    let f₂ ← parser_desc_aux p₂
    return <| concat f₁ f₂
  | quote.1 ((%%ₓp₁) <* %%ₓp₂) => do
    let f₁ ← parser_desc_aux p₁
    let f₂ ← parser_desc_aux p₂
    return <| concat f₁ f₂
  | quote.1 ((%%ₓp₁) *> %%ₓp₂) => do
    let f₁ ← parser_desc_aux p₁
    let f₂ ← parser_desc_aux p₂
    return <| concat f₁ f₂
  | quote.1 ((%%ₓp₁) >> %%ₓp₂) => do
    let f₁ ← parser_desc_aux p₁
    let f₂ ← parser_desc_aux p₂
    return <| concat f₁ f₂
  | quote.1 (many (%%ₓp)) => do
    let f ← parser_desc_aux p
    return [maybe_paren f ++ "*"]
  | quote.1 (optionalₓ (%%ₓp)) => do
    let f ← parser_desc_aux p
    return [maybe_paren f ++ "?"]
  | quote.1 (sep_by (%%ₓsep) (%%ₓp)) => do
    let f₁ ← parser_desc_aux sep
    let f₂ ← parser_desc_aux p
    return [maybe_paren f₂ ++ join f₁, " ..."]
  | quote.1 ((%%ₓp₁) <|> %%ₓp₂) => do
    let f₁ ← parser_desc_aux p₁
    let f₂ ← parser_desc_aux p₂
    return <|
        if f₁ then [maybe_paren f₂ ++ "?"]
        else if f₂ then [maybe_paren f₁ ++ "?"] else [paren <| join <| f₁ ++ [to_fmt " | "] ++ f₂]
  | quote.1 (brackets (%%ₓl) (%%ₓr) (%%ₓp)) => do
    let f ← parser_desc_aux p
    let l ← eval_expr Stringₓ l
    let r ← eval_expr Stringₓ r
    -- much better than the naive [l, " ", f, " ", r]
        return
        [to_fmt l ++ join f ++ to_fmt r]
  | e => do
    let e' ←
      (do
            let e' ← unfold e
            guardₓ <| e' ≠ e
            return e') <|>
          do
          let f ← pp e
          fail <| to_fmt "don't know how to pretty print " ++ f
    parser_desc_aux e'

unsafe def param_desc : expr → tactic format
  | quote.1 (parse (%%ₓp)) => join <$> parser_desc_aux p
  | quote.1 (optParam (%%ₓt) _) => (· ++ "?") <$> pp t
  | e =>
    if is_constant e ∧ (const_name e).components.ilast = `itactic then return <| to_fmt "{ tactic }" else paren <$> pp e

private unsafe axiom parse_binders_core (rbp : ℕ) : parser (List pexpr)

unsafe def parse_binders (rbp := Std.Prec.max) :=
  with_desc "<binders>" (parse_binders_core rbp)

unsafe axiom decl_attributes : Type

unsafe axiom decl_attributes.apply : decl_attributes → Name → parser Unit

unsafe inductive noncomputable_modifier
  | computable
  | noncomputable
  | force_noncomputable

unsafe structure decl_modifiers where
  is_private : Bool
  is_protected : Bool
  is_meta : Bool
  is_mutual : Bool
  is_noncomputable : noncomputable_modifier

unsafe structure decl_meta_info where
  attrs : decl_attributes
  modifiers : decl_modifiers
  doc_string : Option Stringₓ

unsafe structure single_inductive_decl where
  attrs : decl_attributes
  sig : expr
  intros : List expr

unsafe def single_inductive_decl.name (d : single_inductive_decl) : Name :=
  d.sig.app_fn.const_name

unsafe structure inductive_decl where
  u_names : List Name
  params : List expr
  decls : List single_inductive_decl

/--
Parses and elaborates a single or multiple mutual inductive declarations (without the `inductive` keyword), depending on `is_mutual` -/
unsafe axiom inductive_decl.parse : decl_meta_info → parser inductive_decl

end Interactive

section Macros

open InteractionMonad

open Interactive

private unsafe def parse_format : Stringₓ → List Charₓ → parser pexpr
  | Acc, [] => pure (pquote.1 (to_fmt (%%ₓreflect Acc)))
  | Acc, '\n' :: s => do
    let f ← parse_format "" s
    pure (pquote.1 (to_fmt (%%ₓreflect Acc) ++ format.line ++ %%ₓf))
  | Acc, '{' :: '{' :: s => parse_format (Acc ++ "{") s
  | Acc, '{' :: s => do
    let (e, s) ← with_input (lean.parser.pexpr 0) s.asString
    let '}' :: s ← return s.toList | fail "'}' expected"
    let f ← parse_format "" s
    pure (pquote.1 (to_fmt (%%ₓreflect Acc) ++ to_fmt (%%ₓe) ++ %%ₓf))
  | Acc, '}' :: '}' :: s => parse_format (Acc ++ "}") s
  | Acc, '}' :: s => fail "'}}' expected"
  | Acc, c :: s => parse_format (Acc.str c) s

@[user_notation]
unsafe def format_macro (_ : parse <| tk "format!") (s : Stringₓ) : parser pexpr :=
  parse_format "" s.toList

private unsafe def parse_sformat : Stringₓ → List Charₓ → parser pexpr
  | Acc, [] => pure <| pexpr.of_expr (reflect Acc)
  | Acc, '{' :: '{' :: s => parse_sformat (Acc ++ "{") s
  | Acc, '{' :: s => do
    let (e, s) ← with_input (lean.parser.pexpr 0) s.asString
    let '}' :: s ← return s.toList | fail "'}' expected"
    let f ← parse_sformat "" s
    pure (pquote.1 ((%%ₓreflect Acc) ++ toString (%%ₓe) ++ %%ₓf))
  | Acc, '}' :: '}' :: s => parse_sformat (Acc ++ "}") s
  | Acc, '}' :: s => fail "'}}' expected"
  | Acc, c :: s => parse_sformat (Acc.str c) s

@[user_notation]
unsafe def sformat_macro (_ : parse <| tk "sformat!") (s : Stringₓ) : parser pexpr :=
  parse_sformat "" s.toList

end Macros

