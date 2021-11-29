prelude 
import Leanbin.Init.Meta.Tactic

namespace Tactic

unsafe axiom flat_assoc : expr → expr → expr → tactic (expr × expr)

unsafe axiom perm_ac : expr → expr → expr → expr → expr → tactic expr

end Tactic

