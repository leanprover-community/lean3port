/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Control.Monad
import Leanbin.Init.Control.Alternative

open Decidable

universe u v

namespace Option

def getOrElse {α : Type u} : Option α → α → α
  | some x, _ => x
  | none, e => e

def rhoare {α : Type u} : Bool → α → Option α
  | true, a => none
  | false, a => some a

def lhoare {α : Type u} : α → Option α → α
  | a, none => a
  | _, some b => b

protected def orelse {α : Type u} : Option α → Option α → Option α
  | some a, o => some a
  | none, some a => some a
  | none, none => none

end Option

