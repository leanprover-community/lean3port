/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Core
import Leanbin.Init.Logic
import Leanbin.Init.Control.Default
import Leanbin.Init.Data.Basic
import Leanbin.Init.Version
import Leanbin.Init.Propext
import Leanbin.Init.CcLemmas
import Leanbin.Init.Funext
import Leanbin.Init.Control.Combinators
import Leanbin.Init.Function
import Leanbin.Init.Classical
import Leanbin.Init.Util
import Leanbin.Init.Coe
import Leanbin.Init.Wf
import Leanbin.Init.Meta.Default
import Leanbin.Init.Meta.WellFoundedTactics
import Leanbin.Init.Algebra.Default
import Leanbin.Init.Data.Default
import Leanbin.Init.Meta.Float
import Leanbin.Init.Meta.Widget.Default
import Leanbin.Init.Meta.FeatureSearch

#align_import init.default from "leanprover-community/lean"@"885390e749e617b3ace9cd5d33759bbccc609a43"

@[user_attribute]
unsafe def debugger.attr : user_attribute
    where
  Name := `breakpoint
  descr := "breakpoint for debugger"
#align debugger.attr debugger.attr

