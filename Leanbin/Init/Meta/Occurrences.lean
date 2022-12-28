/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.occurrences
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
#align occurrences Occurrences

open Occurrences

def Occurrences.contains : Occurrences → Nat → Bool
  | all, p => true
  | Occurrences.pos ps, p => p ∈ ps
  | Occurrences.neg ps, p => p ∉ ps
#align occurrences.contains Occurrences.contains

instance : Inhabited Occurrences :=
  ⟨all⟩

def occurrencesRepr : Occurrences → String
  | Occurrences.all => "*"
  | Occurrences.pos l => repr l
  | Occurrences.neg l => "-" ++ repr l
#align occurrences_repr occurrencesRepr

instance : Repr Occurrences :=
  ⟨occurrencesRepr⟩

unsafe def occurrences_to_format : Occurrences → format
  | Occurrences.all => to_fmt "*"
  | Occurrences.pos l => to_fmt l
  | Occurrences.neg l => to_fmt "-" ++ to_fmt l
#align occurrences_to_format occurrences_to_format

unsafe instance : has_to_format Occurrences :=
  ⟨occurrences_to_format⟩

open Decidable Tactic

