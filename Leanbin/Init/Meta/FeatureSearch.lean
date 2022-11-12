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
#align feature_search.feature_cfg FeatureSearch.FeatureCfg

unsafe inductive feature
  | const (n : Name)
  | arg (p : Name) (c : Name)
  deriving DecidableEq
#align feature_search.feature feature_search.feature

namespace Feature

protected unsafe def to_string : feature → String
  | const n => n.toString
  | arg p c => p.toString ++ "→" ++ c.toString
#align feature_search.feature.to_string feature_search.feature.to_string

protected unsafe def repr : feature → String
  | const n => "(const `" ++ n.toString ++ ")"
  | arg p c => "(arg `" ++ p.toString ++ " `" ++ c.toString ++ ")"
#align feature_search.feature.repr feature_search.feature.repr

unsafe instance : ToString feature :=
  ⟨feature.to_string⟩

unsafe instance : Repr feature :=
  ⟨feature.repr⟩

unsafe instance : has_to_tactic_format feature :=
  ⟨fun f => pure f.toString⟩

unsafe instance : has_to_format feature :=
  ⟨fun f => f.toString⟩

end Feature

unsafe axiom feature_vec : Type
#align feature_search.feature_vec feature_search.feature_vec

namespace FeatureVec

unsafe axiom of_expr (env : environment) (e : expr) (cfg : FeatureCfg := {  }) : feature_vec
#align feature_search.feature_vec.of_expr feature_search.feature_vec.of_expr

unsafe axiom of_exprs (env : environment) (es : List expr) (cfg : FeatureCfg := {  }) : List feature_vec
#align feature_search.feature_vec.of_exprs feature_search.feature_vec.of_exprs

protected unsafe axiom union (a b : feature_vec) : feature_vec
#align feature_search.feature_vec.union feature_search.feature_vec.union

unsafe instance : Union feature_vec :=
  ⟨feature_vec.union⟩

protected unsafe axiom isect (a b : feature_vec) : feature_vec
#align feature_search.feature_vec.isect feature_search.feature_vec.isect

unsafe instance : Inter feature_vec :=
  ⟨feature_vec.isect⟩

unsafe def of_proof (prf : expr) (cfg : FeatureCfg := {  }) : tactic feature_vec := do
  let ty ← infer_type prf
  let env ← get_env
  pure <| of_expr env ty cfg
#align feature_search.feature_vec.of_proof feature_search.feature_vec.of_proof

unsafe def of_thm (n : Name) (cfg : FeatureCfg := {  }) : tactic feature_vec := do
  let decl ← get_decl n
  let env ← get_env
  pure <| of_expr env decl cfg
#align feature_search.feature_vec.of_thm feature_search.feature_vec.of_thm

protected unsafe axiom to_list (fv : feature_vec) : List feature
#align feature_search.feature_vec.to_list feature_search.feature_vec.to_list

unsafe instance : ToString feature_vec :=
  ⟨toString ∘ feature_vec.to_list⟩

unsafe instance : Repr feature_vec :=
  ⟨repr ∘ feature_vec.to_list⟩

unsafe instance : has_to_tactic_format feature_vec :=
  ⟨pp ∘ feature_vec.to_list⟩

unsafe instance : has_to_format feature_vec :=
  ⟨to_fmt ∘ feature_vec.to_list⟩

end FeatureVec

unsafe axiom feature_stats : Type
#align feature_search.feature_stats feature_search.feature_stats

namespace FeatureStats

unsafe axiom of_feature_vecs (fvs : List feature_vec) : feature_stats
#align feature_search.feature_stats.of_feature_vecs feature_search.feature_stats.of_feature_vecs

unsafe axiom idf (fs : feature_stats) (f : feature) : float
#align feature_search.feature_stats.idf feature_search.feature_stats.idf

unsafe axiom norm (fs : feature_stats) (fv : feature_vec) : float
#align feature_search.feature_stats.norm feature_search.feature_stats.norm

unsafe axiom dotp (fs : feature_stats) (fv1 fv2 : feature_vec) : float
#align feature_search.feature_stats.dotp feature_search.feature_stats.dotp

unsafe axiom cosine_similarity (fs : feature_stats) (fv1 fv2 : feature_vec) : float
#align feature_search.feature_stats.cosine_similarity feature_search.feature_stats.cosine_similarity

unsafe axiom features (fs : feature_stats) : List feature
#align feature_search.feature_stats.features feature_search.feature_stats.features

unsafe def features_with_idf (fs : feature_stats) : List (feature × float) :=
  fs.features.map fun f => (f, fs.idf f)
#align feature_search.feature_stats.features_with_idf feature_search.feature_stats.features_with_idf

unsafe instance : ToString feature_stats :=
  ⟨toString ∘ feature_stats.features_with_idf⟩

unsafe instance : Repr feature_stats :=
  ⟨repr ∘ feature_stats.features_with_idf⟩

unsafe instance : has_to_tactic_format feature_stats :=
  ⟨pp ∘ feature_stats.features_with_idf⟩

unsafe instance : has_to_format feature_stats :=
  ⟨to_fmt ∘ feature_stats.features_with_idf⟩

end FeatureStats

unsafe axiom predictor : Type
#align feature_search.predictor feature_search.predictor

unsafe axiom predictor.predict (p : predictor) (goal : feature_vec) (max_results : ℕ) : List (Name × float)
#align feature_search.predictor.predict feature_search.predictor.predict

inductive PredictorType
  | knn
  | mepo
  | bayes
  deriving DecidableEq
#align feature_search.predictor_type FeatureSearch.PredictorType

structure PredictorCfg extends FeatureCfg where
  type := PredictorType.bayes
#align feature_search.predictor_cfg FeatureSearch.PredictorCfg

end FeatureSearch

open FeatureSearch

unsafe axiom environment.mk_predictor (env : environment) (cfg : PredictorCfg := {  }) : predictor
#align environment.mk_predictor environment.mk_predictor

