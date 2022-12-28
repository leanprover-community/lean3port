/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.control.default
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Control.Applicative
import Leanbin.Init.Control.Functor
import Leanbin.Init.Control.Alternative
import Leanbin.Init.Control.Monad
import Leanbin.Init.Control.Lift
import Leanbin.Init.Control.Lawful
import Leanbin.Init.Control.State
import Leanbin.Init.Control.Id
import Leanbin.Init.Control.Except
import Leanbin.Init.Control.Reader
import Leanbin.Init.Control.Option

