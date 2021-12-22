prelude
import Leanbin.Init.Meta.MkDecEqInstance
import Leanbin.Init.Data.Subtype.Basic

open Tactic Subtype

universe u

instance {α : Type u} {p : α → Prop} [DecidableEq α] : DecidableEq { x : α // p x } := by
  run_tac
    mk_dec_eq_instance

