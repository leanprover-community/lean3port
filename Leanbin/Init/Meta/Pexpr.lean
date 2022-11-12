/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Expr

universe u

/-- Quoted expressions. They can be converted into expressions by using a tactic. -/
@[reducible]
unsafe def pexpr :=
  expr false
#align pexpr pexpr

protected unsafe axiom pexpr.of_expr : expr → pexpr
#align pexpr.of_expr pexpr.of_expr

unsafe axiom pexpr.is_placeholder : pexpr → Bool
#align pexpr.is_placeholder pexpr.is_placeholder

unsafe axiom pexpr.mk_placeholder : pexpr
#align pexpr.mk_placeholder pexpr.mk_placeholder

unsafe axiom pexpr.mk_field_macro : pexpr → Name → pexpr
#align pexpr.mk_field_macro pexpr.mk_field_macro

unsafe axiom pexpr.mk_explicit : pexpr → pexpr
#align pexpr.mk_explicit pexpr.mk_explicit

/-- Choice macros are used to implement overloading. -/
unsafe axiom pexpr.is_choice_macro : pexpr → Bool
#align pexpr.is_choice_macro pexpr.is_choice_macro

/-- Information about unelaborated structure instance expressions. -/
unsafe structure structure_instance_info where
  struct : Option Name := none
  field_names : List Name
  field_values : List pexpr
  sources : List pexpr := []
#align structure_instance_info structure_instance_info

/-- Create a structure instance expression. -/
unsafe axiom pexpr.mk_structure_instance : structure_instance_info → pexpr
#align pexpr.mk_structure_instance pexpr.mk_structure_instance

unsafe axiom pexpr.get_structure_instance_info : pexpr → Option structure_instance_info
#align pexpr.get_structure_instance_info pexpr.get_structure_instance_info

unsafe class has_to_pexpr (α : Sort u) where
  to_pexpr : α → pexpr
#align has_to_pexpr has_to_pexpr

unsafe def to_pexpr {α : Sort u} [has_to_pexpr α] : α → pexpr :=
  has_to_pexpr.to_pexpr
#align to_pexpr to_pexpr

unsafe instance : has_to_pexpr pexpr :=
  ⟨id⟩

unsafe instance : has_to_pexpr expr :=
  ⟨pexpr.of_expr⟩

unsafe instance (α : Sort u) (a : α) : has_to_pexpr (reflected _ a) :=
  ⟨pexpr.of_expr ∘ reflected.to_expr⟩

