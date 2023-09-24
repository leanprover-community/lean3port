/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta.Name
import Init.Meta.Options
import Init.Meta.Format
import Init.Meta.RbMap
import Init.Meta.Level
import Init.Meta.Expr
import Init.Meta.Environment
import Init.Meta.Attribute
import Init.Meta.Tactic
import Init.Meta.ContradictionTactic
import Init.Meta.ConstructorTactic
import Init.Meta.InjectionTactic
import Init.Meta.RelationTactics
import Init.Meta.FunInfo
import Init.Meta.CongrLemma
import Init.Meta.MatchTactic
import Init.Meta.AcTactics
import Init.Meta.Backward
import Init.Meta.RewriteTactic
import Init.Meta.Derive
import Init.Meta.MkDecEqInstance
import Init.Meta.SimpTactic
import Init.Meta.SetGetOptionTactics
import Init.Meta.Interactive
import Leanbin.Init.Meta.Converter.Default
import Init.Meta.Vm
import Init.Meta.CompValueTactics
import Leanbin.Init.Meta.Smt.Default
import Init.Meta.AsyncTactic
import Init.Meta.Ref
import Init.Meta.HoleCommand
import Init.Meta.CongrTactic
import Init.Meta.LocalContext
import Init.Meta.TypeContext
import Init.Meta.InstanceCache
import Init.Meta.ModuleInfo
import Init.Meta.ExprAddress
import Init.Meta.TaggedFormat

#align_import init.meta.default from "leanprover-community/lean"@"6f1b5639005a358db19f183c2d7296cebcb12b39"

