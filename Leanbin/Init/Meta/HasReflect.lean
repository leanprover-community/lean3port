/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

! This file was ported from Lean 3 source module init.meta.has_reflect
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Expr
import Leanbin.Init.Util

universe u v

/--
`has_reflect α` lets you produce an `expr` from an instance of α. That is, it is a function from α to expr such that the expr has type α. -/
@[reducible]
unsafe def has_reflect (α : Sort u) :=
  ∀ a : α, reflected _ a
#align has_reflect has_reflect

unsafe structure reflected_value (α : Type u) where
  val : α
  [reflect : reflected _ val]
#align reflected_value reflected_value

namespace ReflectedValue

unsafe def expr {α : Type u} (v : reflected_value α) : expr :=
  v.reflect
#align reflected_value.expr reflected_value.expr

unsafe def subst {α : Type u} {β : Type v} (f : α → β) [rf : reflected _ f]
    (a : reflected_value α) : reflected_value β :=
  @mk _ (f a.val) (rf.subst a.reflect)
#align reflected_value.subst reflected_value.subst

end ReflectedValue

section

attribute [local semireducible] reflected

unsafe instance nat.reflect : has_reflect ℕ
  | n =>
    if n = 0 then q((0 : ℕ))
    else
      if n = 1 then q((1 : ℕ))
      else
        if n % 2 = 0 then q((bit0 $(nat.reflect n / 2) : ℕ)) else q((bit1 $(nat.reflect n / 2) : ℕ))
#align nat.reflect nat.reflect

unsafe instance unsigned.reflect : has_reflect Unsigned
  | ⟨n, pr⟩ => q(Unsigned.ofNat' n)
#align unsigned.reflect unsigned.reflect

end

/-! Instances that [derive] depends on. All other basic instances are defined at the end of
   derive.lean. -/


unsafe instance name.reflect : has_reflect Name
  | Name.anonymous => q(Name.anonymous)
  | Name.mk_string s n => q(fun n => Name.mk_string s n).subst (name.reflect n)
  | Name.mk_numeral i n => q(fun n => Name.mk_numeral i n).subst (name.reflect n)
#align name.reflect name.reflect

unsafe instance list.reflect {α : Type} [has_reflect α] [reflected _ α] : has_reflect (List α)
  | [] => q([])
  | h :: t => q(fun t => h :: t).subst (list.reflect t)
#align list.reflect list.reflect

unsafe instance punit.reflect : has_reflect PUnit
  | () => q(_)
#align punit.reflect punit.reflect

