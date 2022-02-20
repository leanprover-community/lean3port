/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Data.Repr
import Leanbin.Init.Meta.Format
import Leanbin.Init.Meta.ContradictionTactic
import Leanbin.Init.Meta.ConstructorTactic
import Leanbin.Init.Meta.RelationTactics
import Leanbin.Init.Meta.InjectionTactic

/-- We can specify the scope of application of some tactics using
   the following type.

   - all : all occurrences of a given term are considered.

   - pos [1, 3] : only the first and third occurrences of a given
     term are consiered.

   - neg [2] : all but the second occurrence of a given term
     are considered. -/
inductive Occurrences
  | all
  | Pos : List Nat → Occurrences
  | neg : List Nat → Occurrences

open Occurrences

def Occurrences.contains : Occurrences → Nat → Bool
  | all, p => true
  | Occurrences.pos ps, p => p ∈ ps
  | Occurrences.neg ps, p => p ∉ ps

instance : Inhabited Occurrences :=
  ⟨all⟩

def occurrencesRepr : Occurrences → Stringₓ
  | Occurrences.all => "*"
  | Occurrences.pos l => reprₓ l
  | Occurrences.neg l => "-" ++ reprₓ l

instance : HasRepr Occurrences :=
  ⟨occurrencesRepr⟩

unsafe def occurrences_to_format : Occurrences → format
  | Occurrences.all => to_fmt "*"
  | Occurrences.pos l => to_fmt l
  | Occurrences.neg l => to_fmt "-" ++ to_fmt l

unsafe instance : has_to_format Occurrences :=
  ⟨occurrences_to_format⟩

open Decidable Tactic

