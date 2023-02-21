/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module tools.debugger.util
! leanprover-community/mathlib commit cfa34dc83e0f2ef3c1e45cbe9078e472b041cf07
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

namespace Debugger

def isSpace (c : Char) : Bool :=
  if c = ' ' ∨ c = Char.ofNat 11 ∨ c = '\n' then true else false
#align debugger.is_space Debugger.isSpace

private def split_core : List Char → Option String → List String
  | c :: cs, none =>
    if isSpace c then split_core cs none else split_core cs (some <| String.singleton c)
  | c :: cs, some s => if isSpace c then s :: split_core cs none else split_core cs (s.str c)
  | [], none => []
  | [], some s => [s]
#align debugger.split_core debugger.split_core

def split (s : String) : List String :=
  splitCore s.toList none
#align debugger.split Debugger.split

def toQualifiedNameCore : List Char → Name → String → Name
  | [], r, s => if s.isEmpty then r else .str r s
  | c :: cs, r, s =>
    if isSpace c then to_qualified_name_core cs r s
    else
      if c = '.' then
        if s.isEmpty then to_qualified_name_core cs r ""
        else to_qualified_name_core cs (.str r s) ""
      else to_qualified_name_core cs r (s.str c)
#align debugger.to_qualified_name_core Debugger.toQualifiedNameCore

def toQualifiedName (s : String) : Name :=
  toQualifiedNameCore s.toList Name.anonymous ""
#align debugger.to_qualified_name Debugger.toQualifiedName

def oleanToLean (s : String) :=
  s.popnBack 5 ++ "lean"
#align debugger.olean_to_lean Debugger.oleanToLean

unsafe def get_file (fn : Name) : vm String :=
  (do
      let d ← vm.get_decl fn
      let some n ← return (vm_decl.olean d) |
        failure
      return (olean_to_lean n)) <|>
    return "[current file]"
#align debugger.get_file debugger.get_file

unsafe def pos_info (fn : Name) : vm String :=
  (do
      let d ← vm.get_decl fn
      let some p ← return (vm_decl.pos d) |
        failure
      let file ← get_file fn
      return s! "{file }:{p }:{p}") <|>
    return "<position not available>"
#align debugger.pos_info debugger.pos_info

unsafe def show_fn (header : String) (fn : Name) (frame : Nat) : vm Unit := do
  let pos ← pos_info fn
  vm.put_str s! "[{frame }] {header}"
  if header = "" then return () else vm.put_str " "
  vm.put_str
      s! "{fn } at {Pos}
        "
#align debugger.show_fn debugger.show_fn

unsafe def show_curr_fn (header : String) : vm Unit := do
  let fn ← vm.curr_fn
  let sz ← vm.call_stack_size
  show_fn header fn (sz - 1)
#align debugger.show_curr_fn debugger.show_curr_fn

unsafe def is_valid_fn_prefix (p : Name) : vm Bool := do
  let env ← vm.get_env
  return <|
      env ff fun d r =>
        r ||
          let n := d
          p n
#align debugger.is_valid_fn_prefix debugger.is_valid_fn_prefix

unsafe def show_frame (frame_idx : Nat) : vm Unit := do
  let sz ← vm.call_stack_size
  let fn ← if frame_idx ≥ sz then vm.curr_fn else vm.call_stack_fn frame_idx
  show_fn "" fn frame_idx
#align debugger.show_frame debugger.show_frame

unsafe def type_to_string : Option expr → Nat → vm String
  | none, i => do
    let o ← vm.stack_obj i
    match o with
      | VmObjKind.simple => return "[tagged value]"
      | VmObjKind.constructor => return "[constructor]"
      | VmObjKind.closure => return "[closure]"
      | VmObjKind.native_closure => return "[native closure]"
      | VmObjKind.mpz => return "[big num]"
      | VmObjKind.name => return "name"
      | VmObjKind.level => return "level"
      | VmObjKind.expr => return "expr"
      | VmObjKind.declaration => return "declaration"
      | VmObjKind.environment => return "environment"
      | VmObjKind.tactic_state => return "tactic_state"
      | VmObjKind.format => return "format"
      | VmObjKind.options => return "options"
      | VmObjKind.other => return "[other]"
  | some type, i => do
    let fmt ← vm.pp_expr type
    let opts ← vm.get_options
    return <| fmt opts
#align debugger.type_to_string debugger.type_to_string

unsafe def show_vars_core : Nat → Nat → Nat → vm Unit
  | c, i, e =>
    if i = e then return ()
    else do
      let (n, type) ← vm.stack_obj_info i
      let type_str ← type_to_string type i
      vm.put_str
          s! "#{c } {n } : {type_str}
            "
      show_vars_core (c + 1) (i + 1) e
#align debugger.show_vars_core debugger.show_vars_core

unsafe def show_vars (frame : Nat) : vm Unit := do
  let (s, e) ← vm.call_stack_var_range frame
  show_vars_core 0 s e
#align debugger.show_vars debugger.show_vars

unsafe def show_stack_core : Nat → vm Unit
  | 0 => return ()
  | i + 1 => do
    let fn ← vm.call_stack_fn i
    show_fn "" fn i
    show_stack_core i
#align debugger.show_stack_core debugger.show_stack_core

unsafe def show_stack : vm Unit := do
  let sz ← vm.call_stack_size
  show_stack_core sz
#align debugger.show_stack debugger.show_stack

end Debugger

