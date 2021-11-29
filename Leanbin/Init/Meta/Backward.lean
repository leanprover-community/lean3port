prelude 
import Leanbin.Init.Meta.Tactic 
import Leanbin.Init.Meta.SetGetOptionTactics

namespace Tactic

unsafe axiom back_lemmas : Type

unsafe axiom mk_back_lemmas_core : transparency → tactic back_lemmas

unsafe axiom back_lemmas_insert_core : transparency → back_lemmas → expr → tactic back_lemmas

unsafe axiom back_lemmas_find : back_lemmas → expr → tactic (List expr)

unsafe def mk_back_lemmas : tactic back_lemmas :=
  mk_back_lemmas_core reducible

unsafe def back_lemmas_insert : back_lemmas → expr → tactic back_lemmas :=
  back_lemmas_insert_core reducible

unsafe axiom backward_chaining_core : transparency → Bool → Nat → tactic Unit → tactic Unit → back_lemmas → tactic Unit

unsafe def back_lemmas_add_extra : transparency → back_lemmas → List expr → tactic back_lemmas
| m, bls, [] => return bls
| m, bls, l :: ls =>
  do 
    let new_bls ← back_lemmas_insert_core m bls l 
    back_lemmas_add_extra m new_bls ls

unsafe def back_chaining_core (pre_tactic : tactic Unit) (leaf_tactic : tactic Unit) (extra_lemmas : List expr) :
  tactic Unit :=
  do 
    let intro_lemmas ← mk_back_lemmas_core reducible 
    let new_lemmas ← back_lemmas_add_extra reducible intro_lemmas extra_lemmas 
    let max ← get_nat_option `back_chaining.max_depth 8
    backward_chaining_core reducible tt max pre_tactic leaf_tactic new_lemmas

unsafe def back_chaining : tactic Unit :=
  back_chaining_core skip assumption []

unsafe def back_chaining_using : List expr → tactic Unit :=
  back_chaining_core skip assumption

unsafe def back_chaining_using_hs : tactic Unit :=
  local_context >>= back_chaining_core skip failed

end Tactic

