/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Control.Applicative

universe u v

abbrev HasOrelse := OrElse

section

variable {f : Type u → Type v} [Alternative f] {α : Type u}

@[inline]
def assert {f : Type → Type v} [Alternative f] (p : Prop) [Decidable p] : f (Inhabited p) :=
  if h : p then pure ⟨h⟩ else failure

/- Later we define a coercion from bool to Prop, but this version will still be useful.
   Given (t : tactic bool), we can write t >>= guardb -/
@[inline]
def guardb {f : Type → Type v} [Alternative f] : Bool → f Unit
  | true => pure ()
  | false => failure

end

