/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Option.Basic
import Init.Meta.Lean.Parser
import Init.Meta.Tactic
import Init.Meta.HasReflect

#align_import init.meta.interactive_base from "leanprover-community/lean"@"5b62a41dc8d3982ebd1ec6c243c185344c8e0e9b"

open Lean

open Lean.Parser

local postfix:1024 "?" => optional

local postfix:1024 "*" => many

namespace Interactive

/-- (parse p) as the parameter type of an interactive tactic will instruct the Lean parser
    to run `p` when parsing the parameter and to pass the parsed value as an argument
    to the tactic. -/
@[reducible]
unsafe def parse {α : Type} (p : parser α) [lean.parser.reflectable p] : Type :=
  α
#align interactive.parse interactive.parse

/--
A `loc` is either a 'wildcard', which means "everywhere", or a list of `option name`s. `none` means `target` and `some n` means `n` in the local context.-/
inductive Loc : Type
  | wildcard : loc
  | ns : List (Option Name) → loc
#align interactive.loc Interactive.Loc

unsafe def loc.include_goal : Loc → Bool
  | loc.wildcard => true
  | loc.ns ls => (ls.map Option.isNone).or
#align interactive.loc.include_goal interactive.loc.include_goal

unsafe def loc.get_locals : Loc → tactic (List expr)
  | loc.wildcard => tactic.local_context
  | loc.ns xs =>
    xs.foldlM
      (fun ls n =>
        match n with
        | none => pure ls
        | some n => do
          let l ← tactic.get_local n
          pure <| l :: ls)
      []
#align interactive.loc.get_locals interactive.loc.get_locals

unsafe def loc.apply (hyp_tac : expr → tactic Unit) (goal_tac : tactic Unit) (l : Loc) :
    tactic Unit := do
  let hs ← l.get_locals
  hs hyp_tac
  if l then goal_tac else pure ()
#align interactive.loc.apply interactive.loc.apply

unsafe def loc.try_apply (hyp_tac : expr → tactic Unit) (goal_tac : tactic Unit) (l : Loc) :
    tactic Unit := do
  let hs ← l.get_locals
  let hts := hs.map hyp_tac
  tactic.try_lst <| if l then hts ++ [goal_tac] else hts
#align interactive.loc.try_apply interactive.loc.try_apply

/-- Use `desc` as the interactive description of `p`. -/
unsafe def with_desc {α : Type} (desc : format) (p : parser α) : parser α :=
  p
#align interactive.with_desc interactive.with_desc

unsafe instance with_desc.reflectable {α : Type} (p : parser α) [h : lean.parser.reflectable p]
    (f : format) : reflectable (with_desc f p) :=
  h
#align interactive.with_desc.reflectable interactive.with_desc.reflectable

namespace Types

variable {α β : Type}

-- optimized pretty printer
unsafe def brackets (l r : String) (p : parser α) :=
  tk l *> p <* tk r
#align interactive.types.brackets interactive.types.brackets

unsafe def list_of (p : parser α) :=
  brackets "[" "]" <| sep_by (skip_info (tk ",")) p
#align interactive.types.list_of interactive.types.list_of

/- ./././Mathport/Syntax/Translate/Command.lean:694:29: warning: unsupported: precedence command -/
/- ./././Mathport/Syntax/Translate/Command.lean:694:29: warning: unsupported: precedence command -/
/-- The right-binding power 2 will terminate expressions by
    '<|>' (rbp 2), ';' (rbp 1), and ',' (rbp 0). It should be used for any (potentially)
    trailing expression parameters. -/
unsafe def tac_rbp :=
  2
#align interactive.types.tac_rbp interactive.types.tac_rbp

/-- A 'tactic expression', which uses right-binding power 2 so that it is terminated by
    '<|>' (rbp 2), ';' (rbp 1), and ',' (rbp 0). It should be used for any (potentially)
    trailing expression parameters. -/
unsafe def texpr :=
  parser.pexpr tac_rbp
#align interactive.types.texpr interactive.types.texpr

/-- Parse an identifier or a '_' -/
unsafe def ident_ : parser Name :=
  ident <|> tk "_" *> return `_
#align interactive.types.ident_ interactive.types.ident_

unsafe def using_ident :=
  (tk "using" *> ident)?
#align interactive.types.using_ident interactive.types.using_ident

unsafe def with_ident_list :=
  tk "with" *> ident_* <|> return []
#align interactive.types.with_ident_list interactive.types.with_ident_list

unsafe def without_ident_list :=
  tk "without" *> ident* <|> return []
#align interactive.types.without_ident_list interactive.types.without_ident_list

unsafe def location :=
  tk "at" *>
      (tk "*" *> return Loc.wildcard <|>
        Loc.ns <$> ((with_desc "⊢" <| tk "⊢" <|> tk "|-") *> return none <|> some <$> ident)*) <|>
    return (Loc.ns [none])
#align interactive.types.location interactive.types.location

unsafe def pexpr_list :=
  list_of (parser.pexpr 0)
#align interactive.types.pexpr_list interactive.types.pexpr_list

unsafe def opt_pexpr_list :=
  pexpr_list <|> return []
#align interactive.types.opt_pexpr_list interactive.types.opt_pexpr_list

unsafe def pexpr_list_or_texpr :=
  pexpr_list <|> List.pure <$> texpr
#align interactive.types.pexpr_list_or_texpr interactive.types.pexpr_list_or_texpr

unsafe def only_flag : parser Bool :=
  tk "only" *> return true <|> return false
#align interactive.types.only_flag interactive.types.only_flag

end Types

/- ./././Mathport/Syntax/Translate/Command.lean:694:29: warning: unsupported: precedence command -/
open Expr Format Tactic Types

private unsafe def maybe_paren : List format → format
  | [] => ""
  | [f] => f
  | fs => paren (join fs)

private unsafe def unfold (e : expr) : tactic expr := do
  let expr.const f_name f_lvls ← return e.get_app_fn |
    failed
  let env ← get_env
  let decl ← env.get f_name
  let new_f ← decl.instantiate_value_univ_params f_lvls
  head_beta (expr.mk_app new_f e)

private unsafe def concat (f₁ f₂ : List format) :=
  if f₁.Empty then f₂ else if f₂.Empty then f₁ else f₁ ++ [" "] ++ f₂

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
private unsafe
  def
    parser_desc_aux
    : expr → tactic ( List format )
    | q( ident ) => return [ "id" ]
      | q( ident_ ) => return [ "id" ]
      | q( parser.pexpr $ ( v ) ) => return [ "expr" ]
      | q( small_nat ) => return [ "n" ]
      | q( tk $ ( c ) ) => List.pure <$> to_fmt <$> eval_expr String c
      | q( cur_pos ) => return [ ]
      | q( pure _ ) => return [ ]
      | q( _ <$> $ ( p ) ) => parser_desc_aux p
      | q( skip_info $ ( p ) ) => parser_desc_aux p
      | q( _ <$ $ ( p ) ) => parser_desc_aux p
      | q( set_goal_info_pos $ ( p ) ) => parser_desc_aux p
      | q( with_desc $ ( desc ) $ ( p ) ) => List.pure <$> eval_expr format desc
      |
        q( $ ( p₁ ) <*> $ ( p₂ ) )
        =>
        do let f₁ ← parser_desc_aux p₁ let f₂ ← parser_desc_aux p₂ return <| concat f₁ f₂
      |
        q( $ ( p₁ ) <* $ ( p₂ ) )
        =>
        do let f₁ ← parser_desc_aux p₁ let f₂ ← parser_desc_aux p₂ return <| concat f₁ f₂
      |
        q( $ ( p₁ ) *> $ ( p₂ ) )
        =>
        do let f₁ ← parser_desc_aux p₁ let f₂ ← parser_desc_aux p₂ return <| concat f₁ f₂
      |
        q( $ ( p₁ ) >> $ ( p₂ ) )
        =>
        do let f₁ ← parser_desc_aux p₁ let f₂ ← parser_desc_aux p₂ return <| concat f₁ f₂
      | q( many $ ( p ) ) => do let f ← parser_desc_aux p return [ maybe_paren f ++ "*" ]
      | q( optional $ ( p ) ) => do let f ← parser_desc_aux p return [ maybe_paren f ++ "?" ]
      |
        q( sep_by $ ( sep ) $ ( p ) )
        =>
        do
          let f₁ ← parser_desc_aux sep
            let f₂ ← parser_desc_aux p
            return [ maybe_paren f₂ ++ join f₁ , " ..." ]
      |
        q( $ ( p₁ ) <|> $ ( p₂ ) )
        =>
        do
          let f₁ ← parser_desc_aux p₁
            let f₂ ← parser_desc_aux p₂
            return
              <|
              if
                f₁
                then
                [ maybe_paren f₂ ++ "?" ]
                else
                if
                  f₂
                  then
                  [ maybe_paren f₁ ++ "?" ]
                  else
                  [ paren <| join <| f₁ ++ [ to_fmt " | " ] ++ f₂ ]
      |
        q( brackets $ ( l ) $ ( r ) $ ( p ) )
        =>
        do
          let f ← parser_desc_aux p
            let l ← eval_expr String l
            let r ← eval_expr String r
            return [ to_fmt l ++ join f ++ to_fmt r ]
      |
        e
        =>
        do
          let
              e'
                ←
                ( do let e' ← unfold e guard <| e' ≠ e return e' )
                  <|>
                  do let f ← pp e fail <| to_fmt "don't know how to pretty print " ++ f
            parser_desc_aux e'

unsafe def param_desc : expr → tactic format
  | q(parse $(p)) => join <$> parser_desc_aux p
  | q(optParam $(t) _) => (· ++ "?") <$> pp t
  | e =>
    if is_constant e ∧ (const_name e).components.getLastI = `itactic then
      return <| to_fmt "{ tactic }"
    else paren <$> pp e
#align interactive.param_desc interactive.param_desc

private unsafe axiom parse_binders_core (rbp : ℕ) : parser (List pexpr)

unsafe def parse_binders (rbp := Std.Prec.max) :=
  with_desc "<binders>" (parse_binders_core rbp)
#align interactive.parse_binders interactive.parse_binders

unsafe axiom decl_attributes : Type
#align interactive.decl_attributes interactive.decl_attributes

unsafe axiom decl_attributes.apply : decl_attributes → Name → parser Unit
#align interactive.decl_attributes.apply interactive.decl_attributes.apply

unsafe inductive noncomputable_modifier
  | Computable
  | noncomputable
  | force_noncomputable
#align interactive.noncomputable_modifier interactive.noncomputable_modifier

unsafe structure decl_modifiers where
  is_private : Bool
  is_protected : Bool
  is_meta : Bool
  is_mutual : Bool
  is_noncomputable : noncomputable_modifier
#align interactive.decl_modifiers interactive.decl_modifiers

unsafe structure decl_meta_info where
  attrs : decl_attributes
  modifiers : decl_modifiers
  doc_string : Option String
#align interactive.decl_meta_info interactive.decl_meta_info

unsafe structure single_inductive_decl where
  attrs : decl_attributes
  sig : expr
  intros : List expr
#align interactive.single_inductive_decl interactive.single_inductive_decl

unsafe def single_inductive_decl.name (d : single_inductive_decl) : Name :=
  d.sig.app_fn.const_name
#align interactive.single_inductive_decl.name interactive.single_inductive_decl.name

unsafe structure inductive_decl where
  u_names : List Name
  params : List expr
  decls : List single_inductive_decl
#align interactive.inductive_decl interactive.inductive_decl

/--
Parses and elaborates a single or multiple mutual inductive declarations (without the `inductive` keyword), depending on `is_mutual` -/
unsafe axiom inductive_decl.parse : decl_meta_info → parser inductive_decl
#align interactive.inductive_decl.parse interactive.inductive_decl.parse

end Interactive

section Macros

open InteractionMonad

open Interactive

private unsafe def parse_format : String → List Char → parser pexpr
  | Acc, [] => pure ``(to_fmt $(reflect Acc))
  | Acc, '\n' :: s => do
    let f ← parse_format "" s
    pure ``(to_fmt $(reflect Acc) ++ format.line ++ $(f))
  | Acc, '{' :: '{' :: s => parse_format (Acc ++ "{") s
  | Acc, '{' :: s => do
    let (e, s) ← with_input (lean.parser.pexpr 0) s.asString
    let '}' :: s ← return s.toList |
      fail "'}' expected"
    let f ← parse_format "" s
    pure ``(to_fmt $(reflect Acc) ++ to_fmt $(e) ++ $(f))
  | Acc, '}' :: '}' :: s => parse_format (Acc ++ "}") s
  | Acc, '}' :: s => fail "'}}' expected"
  | Acc, c :: s => parse_format (Acc.str c) s

@[user_notation]
unsafe def format_macro (_ : parse <| tk "format!") (s : String) : parser pexpr :=
  parse_format "" s.toList
#align format_macro format_macro

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
private unsafe
  def
    parse_sformat
    : String → List Char → parser pexpr
    | Acc , [ ] => pure <| pexpr.of_expr ( reflect Acc )
      | Acc , '{' :: '{' :: s => parse_sformat ( Acc ++ "{" ) s
      |
        Acc , '{' :: s
        =>
        do
          let ( e , s ) ← with_input ( lean.parser.pexpr 0 ) s . asString
            let '}' :: s ← return s . toList | fail "'}' expected"
            let f ← parse_sformat "" s
            pure ` `( $ ( reflect Acc ) ++ toString $ ( e ) ++ $ ( f ) )
      | Acc , '}' :: '}' :: s => parse_sformat ( Acc ++ "}" ) s
      | Acc , '}' :: s => fail "'}}' expected"
      | Acc , c :: s => parse_sformat ( Acc . str c ) s

@[user_notation]
unsafe def sformat_macro (_ : parse <| tk "sformat!") (s : String) : parser pexpr :=
  parse_sformat "" s.toList
#align sformat_macro sformat_macro

end Macros

