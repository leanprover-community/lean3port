/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Tactic

namespace Tactic

unsafe def set_bool_option (n : Name) (v : Bool) : tactic Unit := do
  let s ← read
  write <| tactic_state.set_options s (options.set_bool (tactic_state.get_options s) n v)

unsafe def set_nat_option (n : Name) (v : Nat) : tactic Unit := do
  let s ← read
  write <| tactic_state.set_options s (options.set_nat (tactic_state.get_options s) n v)

unsafe def set_string_option (n : Name) (v : Stringₓ) : tactic Unit := do
  let s ← read
  write <| tactic_state.set_options s (options.set_string (tactic_state.get_options s) n v)

unsafe def get_bool_option (n : Name) (default : Bool) : tactic Bool := do
  let s ← read
  return <| options.get_bool (tactic_state.get_options s) n default

unsafe def get_nat_option (n : Name) (default : Nat) : tactic Nat := do
  let s ← read
  return <| options.get_nat (tactic_state.get_options s) n default

unsafe def get_string_option (n : Name) (default : Stringₓ) : tactic Stringₓ := do
  let s ← read
  return <| options.get_string (tactic_state.get_options s) n default

end Tactic

