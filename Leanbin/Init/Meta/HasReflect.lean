/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
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

unsafe structure reflected_value (α : Type u) where
  val : α
  [reflect : reflected _ val]

namespace ReflectedValue

unsafe def expr {α : Type u} (v : reflected_value α) : expr :=
  v.reflect

unsafe def subst {α : Type u} {β : Type v} (f : α → β) [rf : reflected _ f] (a : reflected_value α) :
    reflected_value β :=
  @mk _ (f a.val) (rf.subst a.reflect)

end ReflectedValue

section

attribute [local semireducible] reflected

unsafe instance nat.reflect : has_reflect ℕ
  | n =>
    if n = 0 then quote.1 (0 : ℕ)
    else
      if n = 1 then quote.1 (1 : ℕ)
      else
        if n % 2 = 0 then quote.1 (bit0 (%%ₓnat.reflect (n / 2)) : ℕ) else quote.1 (bit1 (%%ₓnat.reflect (n / 2)) : ℕ)

unsafe instance unsigned.reflect : has_reflect Unsigned
  | ⟨n, pr⟩ => quote.1 (Unsigned.ofNat' n)

end

/- Instances that [derive] depends on. All other basic instances are defined at the end of
   derive.lean. -/
unsafe instance name.reflect : has_reflect Name
  | Name.anonymous => quote.1 Name.anonymous
  | Name.mk_string s n => (quote.1 fun n => Name.mk_string s n).subst (name.reflect n)
  | Name.mk_numeral i n => (quote.1 fun n => Name.mk_numeral i n).subst (name.reflect n)

unsafe instance list.reflect {α : Type} [has_reflect α] [reflected _ α] : has_reflect (List α)
  | [] => quote.1 []
  | h :: t => (quote.1 fun t => h :: t).subst (list.reflect t)

unsafe instance punit.reflect : has_reflect PUnit
  | () => quote.1 _

