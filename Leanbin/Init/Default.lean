/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Logic
import Leanbin.Init.Control.Default
import Init.Data.Basic
import Init.Version
import Init.Propext
import Init.CcLemmas
import Init.Funext
import Init.Control.Combinators
import Logic.Function.Defs
import Init.Classical
import Init.Util
import Init.Coe
import Init.Wf
import Leanbin.Init.Meta.Default
import Init.Meta.WellFoundedTactics
import Leanbin.Init.Algebra.Default
import Leanbin.Init.Data.Default
import Init.Meta.Float
import Leanbin.Init.Meta.Widget.Default
import Init.Meta.FeatureSearch

#align_import init.default from "leanprover-community/lean"@"885390e749e617b3ace9cd5d33759bbccc609a43"

@[user_attribute]
unsafe def debugger.attr : user_attribute
    where
  Name := `breakpoint
  descr := "breakpoint for debugger"
#align debugger.attr debugger.attr

