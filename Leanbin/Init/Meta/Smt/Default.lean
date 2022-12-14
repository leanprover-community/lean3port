/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.smt.default
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Meta.Smt.CongruenceClosure
import Leanbin.Init.CcLemmas
import Leanbin.Init.Meta.Smt.Ematch
import Leanbin.Init.Meta.Smt.SmtTactic
import Leanbin.Init.Meta.Smt.Interactive
import Leanbin.Init.Meta.Smt.Rsimp

