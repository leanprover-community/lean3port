/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import Leanbin.Init.Logic

open Decidable

universe u

namespace Subtype

theorem exists_of_subtype {α : Type u} {p : α → Prop} : { x // p x } → ∃ x, p x
  | ⟨a, h⟩ => ⟨a, h⟩

variable {α : Type u} {p : α → Prop}

theorem tag_irrelevant {a : α} (h1 h2 : p a) : mk a h1 = mk a h2 :=
  rfl

protected theorem eq : ∀ {a1 a2 : { x // p x }}, val a1 = val a2 → a1 = a2
  | ⟨x, h1⟩, ⟨x, h2⟩, rfl => rfl

theorem ne_of_val_ne {a1 a2 : { x // p x }} : val a1 ≠ val a2 → a1 ≠ a2 :=
  mt <| congr_arg _

theorem eta (a : { x // p x }) (h : p (val a)) : mk (val a) h = a :=
  Subtype.eq rfl

end Subtype

open Subtype

def Subtype.inhabited {α : Type u} {p : α → Prop} {a : α} (h : p a) : Inhabited { x // p x } :=
  ⟨⟨a, h⟩⟩

