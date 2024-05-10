
#align_import smt.prove from "leanprover-community/lean"@"76eed7cb41effca75066a0f6b83e921f133a6d58"

namespace Smt

open Tactic

private unsafe def collect_props : List expr → tactic (List expr)
  | [] => return []
  | H :: Hs => do
    let Eqs ← collect_props Hs
    let Htype ← infer_type H >>= infer_type >>= whnf
    return <| if Htype = q(Prop) then H :: Eqs else Eqs

/- ././././Mathport/Syntax/Translate/Expr.lean:338:4: warning: unsupported (TODO): `[tacs] -/
-- This tactic is just a placeholder, designed to be modified for specific performance experiments
unsafe def prove : tactic Unit := do
  local_context >>= collect_props >>= revert_lst
  trace "SMT state, after reverting propositions:"
  trace_state
  sorry
#align smt.prove smt.prove

end Smt

