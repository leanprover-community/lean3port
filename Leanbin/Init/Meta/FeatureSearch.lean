/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.Derive
import Leanbin.Init.Meta.MkDecEqInstance
import Leanbin.Init.Meta.Float

namespace FeatureSearch

open Tactic Native

structure FeatureCfg where
  ignoreTc := true
  ignorePiDomain := true
  ignoreTypeArgs := true
  ignoreDecidable := true
  ignoreConns := true

unsafe inductive feature
  | const (n : Name)
  | arg (p : Name) (c : Name)
  deriving DecidableEq

namespace Feature

protected unsafe def to_string : feature → Stringₓ
  | const n => n.toString
  | arg p c => p.toString ++ "→" ++ c.toString

protected unsafe def repr : feature → Stringₓ
  | const n => "(const `" ++ n.toString ++ ")"
  | arg p c => "(arg `" ++ p.toString ++ " `" ++ c.toString ++ ")"

unsafe instance : HasToString feature :=
  ⟨feature.to_string⟩

unsafe instance : HasRepr feature :=
  ⟨feature.repr⟩

unsafe instance : has_to_tactic_format feature :=
  ⟨fun f => pure f.toString⟩

unsafe instance : has_to_format feature :=
  ⟨fun f => f.toString⟩

end Feature

unsafe axiom feature_vec : Type

namespace FeatureVec

unsafe axiom of_expr (env : environment) (e : expr) (cfg : FeatureCfg := {  }) : feature_vec

unsafe axiom of_exprs (env : environment) (es : List expr) (cfg : FeatureCfg := {  }) : List feature_vec

protected unsafe axiom union (a b : feature_vec) : feature_vec

unsafe instance : HasUnion feature_vec :=
  ⟨feature_vec.union⟩

protected unsafe axiom isect (a b : feature_vec) : feature_vec

unsafe instance : HasInter feature_vec :=
  ⟨feature_vec.isect⟩

unsafe def of_proof (prf : expr) (cfg : FeatureCfg := {  }) : tactic feature_vec := do
  let ty ← infer_type prf
  let env ← get_env
  pure <| of_expr env ty cfg

unsafe def of_thm (n : Name) (cfg : FeatureCfg := {  }) : tactic feature_vec := do
  let decl ← get_decl n
  let env ← get_env
  pure <| of_expr env decl cfg

protected unsafe axiom to_list (fv : feature_vec) : List feature

unsafe instance : HasToString feature_vec :=
  ⟨toString ∘ feature_vec.to_list⟩

unsafe instance : HasRepr feature_vec :=
  ⟨reprₓ ∘ feature_vec.to_list⟩

unsafe instance : has_to_tactic_format feature_vec :=
  ⟨pp ∘ feature_vec.to_list⟩

unsafe instance : has_to_format feature_vec :=
  ⟨to_fmt ∘ feature_vec.to_list⟩

end FeatureVec

unsafe axiom feature_stats : Type

namespace FeatureStats

unsafe axiom of_feature_vecs (fvs : List feature_vec) : feature_stats

unsafe axiom idf (fs : feature_stats) (f : feature) : float

unsafe axiom norm (fs : feature_stats) (fv : feature_vec) : float

unsafe axiom dotp (fs : feature_stats) (fv1 fv2 : feature_vec) : float

unsafe axiom cosine_similarity (fs : feature_stats) (fv1 fv2 : feature_vec) : float

unsafe axiom features (fs : feature_stats) : List feature

unsafe def features_with_idf (fs : feature_stats) : List (feature × float) :=
  fs.features.map fun f => (f, fs.idf f)

unsafe instance : HasToString feature_stats :=
  ⟨toString ∘ feature_stats.features_with_idf⟩

unsafe instance : HasRepr feature_stats :=
  ⟨reprₓ ∘ feature_stats.features_with_idf⟩

unsafe instance : has_to_tactic_format feature_stats :=
  ⟨pp ∘ feature_stats.features_with_idf⟩

unsafe instance : has_to_format feature_stats :=
  ⟨to_fmt ∘ feature_stats.features_with_idf⟩

end FeatureStats

unsafe axiom predictor : Type

unsafe axiom predictor.predict (p : predictor) (goal : feature_vec) (max_results : ℕ) : List (Name × float)

inductive PredictorType
  | knn
  | mepo
  | bayes
  deriving DecidableEq

structure PredictorCfg extends FeatureCfg where
  type := PredictorType.bayes

end FeatureSearch

open FeatureSearch

unsafe axiom environment.mk_predictor (env : environment) (cfg : PredictorCfg := {  }) : predictor

