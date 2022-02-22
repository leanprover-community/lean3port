/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.Format
import Leanbin.Init.Function

structure ParamInfo where
  isImplicit : Bool
  -- is an implicit parameter.
  isInstImplicit : Bool
  -- is a typeclass instance
  isProp : Bool
  hasFwdDeps : Bool
  isDecInst : Bool
  backDeps : List Nat

-- previous parameters it depends on
open Format List Decidable

private unsafe def ppfield {α : Type} [has_to_format α] (fname : Stringₓ) (v : α) : format :=
  group <| to_fmt fname ++ space ++ to_fmt ":=" ++ space ++ nest (fname.length + 4) (to_fmt v)

private unsafe def concat_fields (f₁ f₂ : format) : format :=
  if is_nil f₁ then f₂ else if is_nil f₂ then f₁ else f₁ ++ to_fmt "," ++ line ++ f₂

-- mathport name: «expr +++ »
local infixl:65 "+++" => concat_fields

unsafe def param_info.to_format : ParamInfo → format
  | ParamInfo.mk i ii p d di ds =>
    group ∘ cbrace <|
      when i
                  "implicit"+++when ii
                  "inst_implicit"+++when p
                "prop"+++when d
              "has_fwd_deps"+++when di "is_dec_inst"+++when (length ds > 0) (to_fmt "back_deps := " ++ to_fmt ds)

unsafe instance : has_to_format ParamInfo :=
  has_to_format.mk param_info.to_format

structure FunInfo where
  params : List ParamInfo
  resultDeps : List Nat

-- parameters the result type depends on
unsafe def fun_info_to_format : FunInfo → format
  | FunInfo.mk ps ds => group ∘ dcbrace <| ppfield "params" ps+++ppfield "result_deps" ds

unsafe instance : has_to_format FunInfo :=
  has_to_format.mk fun_info_to_format

/-- specialized is true if the result of fun_info has been specifialized
  using this argument.
  For example, consider the function

             f : Pi (α : Type), α -> α

  Now, suppse we request get_specialize fun_info for the application

         f unit a

  fun_info_manager returns two param_info objects:
  1) specialized = true
  2) is_subsingleton = true

  Note that, in general, the second argument of f is not a subsingleton,
  but it is in this particular case/specialization.

  \remark This bit is only set if it is a dependent parameter.

   Moreover, we only set is_specialized IF another parameter
   becomes a subsingleton -/
structure SubsingletonInfo where
  specialized : Bool
  isSubsingleton : Bool

unsafe def subsingleton_info_to_format : SubsingletonInfo → format
  | SubsingletonInfo.mk s ss => group ∘ cbrace <| when s "specialized"+++when ss "subsingleton"

unsafe instance : has_to_format SubsingletonInfo :=
  has_to_format.mk subsingleton_info_to_format

namespace Tactic

/-- If nargs is not none, then return information assuming the function has only nargs arguments. -/
unsafe axiom get_fun_info (f : expr) (nargs : Option Nat := none) (md := semireducible) : tactic FunInfo

unsafe axiom get_subsingleton_info (f : expr) (nargs : Option Nat := none) (md := semireducible) :
    tactic (List SubsingletonInfo)

/-- `get_spec_subsingleton_info t` return subsingleton parameter
   information for the function application t of the form
      `f a_1 ... a_n`.

    This tactic is more precise than `get_subsingleton_info f` and `get_subsingleton_info_n f n`

    Example: given `f : Pi (α : Type), α -> α`, `get_spec_subsingleton_info` for

    `f unit b`

    returns a fun_info with two param_info
    1) specialized = tt
    2) is_subsingleton = tt

    The second argument is marked as subsingleton only because the resulting information
    is taking into account the first argument. -/
unsafe axiom get_spec_subsingleton_info (t : expr) (md := semireducible) : tactic (List SubsingletonInfo)

unsafe axiom get_spec_prefix_size (t : expr) (nargs : Nat) (md := semireducible) : tactic Nat

private unsafe def is_next_explicit : List ParamInfo → Bool
  | [] => true
  | p :: ps => bnot p.isImplicit && bnot p.isInstImplicit

unsafe def fold_explicit_args_aux {α} (f : α → expr → tactic α) : List expr → List ParamInfo → α → tactic α
  | [], _, a => return a
  | e :: es, ps, a =>
    if is_next_explicit ps then f a e >>= fold_explicit_args_aux es ps.tail else fold_explicit_args_aux es ps.tail a

unsafe def fold_explicit_args {α} (e : expr) (a : α) (f : α → expr → tactic α) : tactic α :=
  if e.is_app then do
    let info ← get_fun_info e.get_app_fn (some e.get_app_num_args)
    fold_explicit_args_aux f e info a
  else return a

end Tactic

