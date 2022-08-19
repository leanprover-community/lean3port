/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Leanbin.Init.Data.List.Lemmas

open List

universe u v

instance : Monad List where
  pure := @List.ret
  map := @List.map
  bind := @List.bind

@[simp] protected theorem List.ret_def : (.ret a : List α) = [a] := rfl
@[simp] protected theorem List.pure_def : (pure a : List α) = [a] := rfl
@[simp] protected theorem List.map_def {f : α → β} : (f <$> a : List β) = map f a := rfl
@[simp] protected theorem List.bind_def {f : α → List β} : (a >>= f : List β) = List.bind a f := rfl

@[simp] theorem List.bind_singleton (xs : List α) (f : α → β) : xs.bind ([f ·]) = xs.map f := by
  induction xs <;> simp_all

theorem List.bind_bind (xs : List α) (f : α → List β) (g : β → List γ) :
    (xs.bind f).bind g = xs.bind fun x => (f x).bind g := by
  induction xs <;> simp_all

theorem List.map_bind (xs : List α) (f : α → β) (g : β → List γ) :
    (xs.map f).bind g = xs.bind fun x => g (f x) := by
  induction xs <;> simp_all

instance : LawfulMonad List where
  id_map := by simp
  pure_bind := by simp
  bind_assoc := by simp [List.bind_bind]
  map_const := by simp [Functor.mapConst, Functor.map]
  comp_map := by simp
  seqLeft_eq := by simp [SeqLeft.seqLeft, Seq.seq, List.map_bind, Function.const]
  seqRight_eq := by simp [SeqRight.seqRight, Seq.seq, List.map_bind]
  pure_seq := by simp [Seq.seq]
  map_pure := by simp
  seq_pure := by simp [Seq.seq]
  seq_assoc := by simp [Seq.seq, List.map_bind, List.bind_bind, List.bind_map]
  bind_pure_comp := by simp
  bind_map := by simp [Seq.seq]

instance : Alternative List where
  failure := []
  orElse a b := a ++ b ()
