/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers

! This file was ported from Lean 3 source module init.meta.tagged_format
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.ExprAddress
import Leanbin.Init.Control.Default

universe u

/-- An alternative to format that keeps structural information stored as a tag. -/
unsafe inductive tagged_format (α : Type u)
  | tag : α → tagged_format → tagged_format
  | compose : tagged_format → tagged_format → tagged_format
  | Group : tagged_format → tagged_format
  | nest : Nat → tagged_format → tagged_format
  | highlight : Format.Color → tagged_format → tagged_format
  | of_format : format → tagged_format
#align tagged_format tagged_format

namespace TaggedFormat

variable {α β : Type u}

protected unsafe def map (f : α → β) : tagged_format α → tagged_format β
  | compose x y => compose (map x) (map y)
  | Group x => Group <| map x
  | nest i x => nest i <| map x
  | highlight c x => highlight c <| map x
  | of_format x => of_format x
  | tag a x => tag (f a) (map x)
#align tagged_format.map tagged_format.map

unsafe instance is_functor : Functor tagged_format where map := @tagged_format.map
#align tagged_format.is_functor tagged_format.is_functor

unsafe def m_untag {t : Type → Type} [Monad t] (f : α → format → t format) :
    tagged_format α → t format
  | compose x y => pure format.compose <*> m_untag x <*> m_untag y
  | Group x => pure format.group <*> m_untag x
  | nest i x => pure (format.nest i) <*> m_untag x
  | highlight c x => pure format.highlight <*> m_untag x <*> pure c
  | of_format x => pure <| x
  | tag a x => m_untag x >>= f a
#align tagged_format.m_untag tagged_format.m_untag

unsafe def untag (f : α → format → format) : tagged_format α → format :=
  @m_untag _ id _ f
#align tagged_format.untag tagged_format.untag

unsafe instance has_to_fmt : has_to_format (tagged_format α) :=
  ⟨tagged_format.untag fun a f => f⟩
#align tagged_format.has_to_fmt tagged_format.has_to_fmt

end TaggedFormat

/-- tagged_format with information about subexpressions. -/
unsafe def eformat :=
  tagged_format (Expr.Address × expr)
#align eformat eformat

/-- A special version of pp which also preserves expression boundary information.

On a tag ⟨e,a⟩, note that the given expr `e` is _not_ necessarily the subexpression of the root
expression that `tactic_state.pp_tagged` was called with. For example if the subexpression is
under a binder then all of the `expr.var 0`s will be replaced with a local constant not in
the local context with the name and type set to that of the binder.-/
unsafe axiom tactic_state.pp_tagged : tactic_state → expr → eformat
#align tactic_state.pp_tagged tactic_state.pp_tagged

unsafe def tactic.pp_tagged : expr → tactic eformat
  | e => tactic.read >>= fun ts => pure <| tactic_state.pp_tagged ts e
#align tactic.pp_tagged tactic.pp_tagged

