prelude 
import Leanbin.Init.Meta.Tactic 
import Leanbin.Init.Meta.CongrLemma 
import Leanbin.Init.Meta.RelationTactics 
import Leanbin.Init.Function

namespace Tactic

unsafe def apply_congr_core (clemma : congr_lemma) : tactic Unit :=
  do 
    assert `H_congr_lemma clemma.type 
    exact clemma.proof 
    get_local `H_congr_lemma >>= apply 
    all_goals'$
        do 
          try (applyc `heq_of_eq)
          get_local `H_congr_lemma >>= clear

unsafe def apply_eq_congr_core (tgt : expr) : tactic Unit :=
  do 
    let (lhs, rhs) ← match_eq tgt 
    guardₓ lhs.is_app 
    let clemma ← mk_specialized_congr_lemma lhs 
    apply_congr_core clemma

unsafe def apply_heq_congr_core : tactic Unit :=
  do 
    try (applyc `eq_of_heq)
    let (α, lhs, β, rhs) ← target >>= match_heq 
    guardₓ lhs.is_app 
    let clemma ← mk_hcongr_lemma lhs.get_app_fn lhs.get_app_num_args 
    apply_congr_core clemma

unsafe def congr_core : tactic Unit :=
  do 
    let tgt ← target 
    apply_eq_congr_core tgt <|> apply_heq_congr_core <|> fail "congr tactic failed"

unsafe def congr : tactic Unit :=
  do 
    focus1 (try assumption >> congr_core >> all_goals' (try reflexivity >> try congr))

end Tactic

