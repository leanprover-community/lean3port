
namespace Smt

open Tactic

private unsafe def collect_props : List expr → tactic (List expr)
  | [] => return []
  | H :: Hs => do
    let Eqs ← collect_props Hs
    let Htype ← infer_type H >>= infer_type >>= whnf
    return $ if Htype = q(Prop) then H :: Eqs else Eqs
#align smt.collect_props smt.collect_props

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
-- This tactic is just a placeholder, designed to be modified for specific performance experiments
unsafe def prove : tactic Unit := do
  local_context >>= collect_props >>= revert_lst
  trace "SMT state, after reverting propositions:"
  trace_state
  sorry
#align smt.prove smt.prove

end Smt

