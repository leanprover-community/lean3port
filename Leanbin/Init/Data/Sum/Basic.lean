/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
prelude
import Leanbin.Init.Logic

universe u v

variable {α : Type u} {β : Type v}

instance Sum.inhabitedLeft [h : Inhabited α] : Inhabited (Sum α β) :=
  ⟨Sum.inl default⟩

instance Sum.inhabitedRight [h : Inhabited β] : Inhabited (Sum α β) :=
  ⟨Sum.inr default⟩

