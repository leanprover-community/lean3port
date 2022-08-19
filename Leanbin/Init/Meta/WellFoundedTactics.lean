/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Default
import Leanbin.Init.Data.Sigma.Lex
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Data.List.Instances
import Leanbin.Init.Data.List.Qsort

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. 
-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.lt_add_of_zero_lt_left (a b : Nat) (h : 0 < b) : a < a + b :=
  show a + 0 < a + b by
    apply Nat.add_lt_add_left
    assumption

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.zero_lt_one_add (a : Nat) : 0 < 1 + a :=
  suffices 0 < a + 1 by
    simp [← Nat.add_comm]
    assumption
  Nat.zero_lt_succ _

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.lt_add_left (a b c : Nat) : a < b → a < c + b := fun h => lt_of_lt_of_le h (Nat.le_add_left _ _)

