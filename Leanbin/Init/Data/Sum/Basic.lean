/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
prelude
import Leanbin.Init.Logic

-- mathport name: «expr ⊕ »
infixr:30 " ⊕ " => Sum

universe u v

variable {α : Type u} {β : Type v}

#print Sum.inhabitedLeft /-
instance Sum.inhabitedLeft [h : Inhabited α] : Inhabited (α ⊕ β) :=
  ⟨Sum.inl default⟩
#align sum.inhabited_left Sum.inhabitedLeft
-/

#print Sum.inhabitedRight /-
instance Sum.inhabitedRight [h : Inhabited β] : Inhabited (α ⊕ β) :=
  ⟨Sum.inr default⟩
#align sum.inhabited_right Sum.inhabitedRight
-/

