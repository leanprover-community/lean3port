/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Simple command line interface for debugging Lean programs and tactics.
-/
import Leanbin.Tools.Debugger.Util

namespace Debugger

inductive Mode
  | init
  | step
  | run
  | done
  deriving DecidableEq

structure State where
  md : Mode
  csz : Nat
  fnBps : List Name
  activeBps : List (Nat × Name)

def initState : State where
  md := Mode.init
  csz := 0
  fnBps := []
  activeBps := []

unsafe def show_help : vm Unit := do
  vm.put_str "exit       - stop debugger\n"
  vm.put_str "help       - display this message\n"
  vm.put_str "run        - continue execution\n"
  vm.put_str "step       - execute until another function in on the top of the stack\n"
  vm.put_str "stack trace\n"
  vm.put_str " up        - move up in the stack trace\n"
  vm.put_str " down      - move down in the stack trace\n"
  vm.put_str " vars      - display variables in the current stack frame\n"
  vm.put_str " stack     - display all functions on the call stack\n"
  vm.put_str " print var - display the value of variable named 'var' in the current stack frame\n"
  vm.put_str " pidx  idx - display the value of variable at position #idx in the current stack frame\n"
  vm.put_str "breakpoints\n"
  vm.put_str " break fn  - add breakpoint for fn\n"
  vm.put_str " rbreak fn - remove breakpoint\n"
  vm.put_str " bs        - show breakpoints\n"

unsafe def add_breakpoint (s : State) (args : List Stringₓ) : vm State :=
  match args with
  | [arg] => do
    let fn ← return <| toQualifiedName arg
    let ok ← is_valid_fn_prefix fn
    if ok then return { s with fnBps := fn :: List.filterₓ (fun fn' => fn ≠ fn') s }
      else vm.put_str "invalid 'break' command, given name is not the prefix for any function\n" >> return s
  | _ => vm.put_str "invalid 'break <fn>' command, incorrect number of arguments\n" >> return s

unsafe def remove_breakpoint (s : State) (args : List Stringₓ) : vm State :=
  match args with
  | [arg] => do
    let fn ← return <| toQualifiedName arg
    return { s with fnBps := List.filterₓ (fun fn' => fn ≠ fn') s }
  | _ => vm.put_str "invalid 'rbreak <fn>' command, incorrect number of arguments\n" >> return s

unsafe def show_breakpoints : List Name → vm Unit
  | [] => return ()
  | fn :: fns => do
    vm.put_str "  "
    vm.put_str fn
    vm.put_str "\n"
    show_breakpoints fns

unsafe def up_cmd (frame : Nat) : vm Nat :=
  if frame = 0 then return 0 else show_frame (frame - 1) >> return (frame - 1)

unsafe def down_cmd (frame : Nat) : vm Nat := do
  let sz ← vm.call_stack_size
  if frame ≥ sz - 1 then return frame else show_frame (frame + 1) >> return (frame + 1)

unsafe def pidx_cmd : Nat → List Stringₓ → vm Unit
  | frame, [arg] => do
    let idx ← return <| arg.toNat
    let sz ← vm.stack_size
    let (bp, ep) ← vm.call_stack_var_range frame
    if bp + idx ≥ ep then vm.put_str "invalid 'pidx <idx>' command, index out of bounds\n"
      else do
        let v ← vm.pp_stack_obj (bp + idx)
        let (n, t) ← vm.stack_obj_info (bp + idx)
        let opts ← vm.get_options
        vm.put_str n
        vm.put_str " := "
        vm.put_str <| v opts
        vm.put_str "\n"
  | _, _ => vm.put_str "invalid 'pidx <idx>' command, incorrect number of arguments\n"

unsafe def print_var : Nat → Nat → Name → vm Unit
  | i, ep, v => do
    if i = ep then vm.put_str "invalid 'print <var>', unknown variable\n"
      else do
        let (n, t) ← vm.stack_obj_info i
        if n = v then do
            let v ← vm.pp_stack_obj i
            let opts ← vm.get_options
            vm.put_str n
            vm.put_str " := "
            vm.put_str <| v opts
            vm.put_str "\n"
          else print_var (i + 1) ep v

unsafe def print_cmd : Nat → List Stringₓ → vm Unit
  | frame, [arg] => do
    let (bp, ep) ← vm.call_stack_var_range frame
    print_var bp ep (to_qualified_name arg)
  | _, _ => vm.put_str "invalid 'print <var>' command, incorrect number of arguments\n"

unsafe def cmd_loop_core : State → Nat → List Stringₓ → vm State
  | s, frame, default_cmd => do
    let is_eof ← vm.eof
    if is_eof then do
        vm.put_str "stopping debugger... 'end of file' has been found\n"
        return { s with md := mode.done }
      else do
        vm.put_str "% "
        let l ← vm.get_line
        let tks ← return <| split l
        let tks ← return <| if tks = [] then default_cmd else tks
        match tks with
          | [] => cmd_loop_core s frame default_cmd
          | cmd :: args =>
            if cmd = "help" ∨ cmd = "h" then show_help >> cmd_loop_core s frame []
            else
              if cmd = "exit" then return { s with md := mode.done }
              else
                if cmd = "run" ∨ cmd = "r" then return { s with md := mode.run }
                else
                  if cmd = "step" ∨ cmd = "s" then return { s with md := mode.step }
                  else
                    if cmd = "break" ∨ cmd = "b" then do
                      let new_s ← add_breakpoint s args
                      cmd_loop_core new_s frame []
                    else
                      if cmd = "rbreak" then do
                        let new_s ← remove_breakpoint s args
                        cmd_loop_core new_s frame []
                      else
                        if cmd = "bs" then do
                          vm.put_str "breakpoints\n"
                          show_breakpoints s
                          cmd_loop_core s frame default_cmd
                        else
                          if cmd = "up" ∨ cmd = "u" then do
                            let frame ← up_cmd frame
                            cmd_loop_core s frame ["u"]
                          else
                            if cmd = "down" ∨ cmd = "d" then do
                              let frame ← down_cmd frame
                              cmd_loop_core s frame ["d"]
                            else
                              if cmd = "vars" ∨ cmd = "v" then do
                                show_vars frame
                                cmd_loop_core s frame []
                              else
                                if cmd = "stack" then do
                                  show_stack
                                  cmd_loop_core s frame []
                                else
                                  if cmd = "pidx" then do
                                    pidx_cmd frame args
                                    cmd_loop_core s frame []
                                  else
                                    if cmd = "print" ∨ cmd = "p" then do
                                      print_cmd frame args
                                      cmd_loop_core s frame []
                                    else do
                                      vm.put_str "unknown command, type 'help' for help\n"
                                      cmd_loop_core s frame default_cmd

unsafe def cmd_loop (s : State) (default_cmd : List Stringₓ) : vm State := do
  let csz ← vm.call_stack_size
  cmd_loop_core s (csz - 1) default_cmd

def pruneActiveBpsCore (csz : Nat) : List (Nat × Name) → List (Nat × Name)
  | [] => []
  | (csz', n) :: ls => if csz < csz' then prune_active_bps_core ls else (csz', n) :: ls

unsafe def prune_active_bps (s : State) : vm State := do
  let sz ← vm.call_stack_size
  return { s with activeBps := prune_active_bps_core sz s }

unsafe def updt_csz (s : State) : vm State := do
  let sz ← vm.call_stack_size
  return { s with csz := sz }

unsafe def init_transition (s : State) : vm State := do
  let opts ← vm.get_options
  if opts `server ff then return { s with md := mode.done }
    else do
      let bps ← vm.get_attribute `breakpoint
      let new_s ← return { s with fnBps := bps }
      if opts `debugger.autorun ff then return { new_s with md := mode.run }
        else do
          vm.put_str "Lean debugger\n"
          show_curr_fn "debugging"
          vm.put_str "type 'help' for help\n"
          cmd_loop new_s []

unsafe def step_transition (s : State) : vm State := do
  let sz ← vm.call_stack_size
  if sz = s then return s
    else do
      show_curr_fn "step"
      cmd_loop s ["s"]

unsafe def bp_reached (s : State) : vm Bool :=
  (do
      let fn ← vm.curr_fn
      return <| s fun p => p fn) <|>
    return false

unsafe def in_active_bps (s : State) : vm Bool := do
  let sz ← vm.call_stack_size
  match s with
    | [] => return ff
    | (csz, _) :: _ => return (sz = csz)

unsafe def run_transition (s : State) : vm State := do
  let b1 ← in_active_bps s
  let b2 ← bp_reached s
  if b1 ∨ Not b2 then return s
    else do
      show_curr_fn "breakpoint"
      let fn ← vm.curr_fn
      let sz ← vm.call_stack_size
      let new_s ← return <| { s with activeBps := (sz, fn) :: s }
      cmd_loop new_s ["r"]

unsafe def step_fn (s : State) : vm State := do
  let s ← prune_active_bps s
  if s = mode.init then do
      let new_s ← init_transition s
      updt_csz new_s
    else
      if s = mode.done then return s
      else
        if s = mode.step then do
          let new_s ← step_transition s
          updt_csz new_s
        else
          if s = mode.run then do
            let new_s ← run_transition s
            updt_csz new_s
          else return s

@[vm_monitor]
unsafe def monitor : vm_monitor State where
  init := initState
  step := step_fn

end Debugger

