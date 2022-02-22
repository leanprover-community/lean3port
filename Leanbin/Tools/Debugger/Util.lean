/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

namespace Debugger

def isSpace (c : Charₓ) : Bool :=
  if c = ' ' ∨ c = Charₓ.ofNat 11 ∨ c = '\n' then true else false

private def split_core : List Charₓ → Option Stringₓ → List Stringₓ
  | c :: cs, none => if isSpace c then split_core cs none else split_core cs (some <| Stringₓ.singleton c)
  | c :: cs, some s => if isSpace c then s :: split_core cs none else split_core cs (s.str c)
  | [], none => []
  | [], some s => [s]

def split (s : Stringₓ) : List Stringₓ :=
  splitCore s.toList none

def toQualifiedNameCore : List Charₓ → Name → Stringₓ → Name
  | [], r, s => if s.isEmpty then r else mkStrName r s
  | c :: cs, r, s =>
    if isSpace c then to_qualified_name_core cs r s
    else
      if c = '.' then if s.isEmpty then to_qualified_name_core cs r "" else to_qualified_name_core cs (mkStrName r s) ""
      else to_qualified_name_core cs r (s.str c)

def toQualifiedName (s : Stringₓ) : Name :=
  toQualifiedNameCore s.toList Name.anonymous ""

def oleanToLean (s : Stringₓ) :=
  s.popnBack 5 ++ "lean"

unsafe def get_file (fn : Name) : vm Stringₓ :=
  (do
      let d ← vm.get_decl fn
      let some n ← return (vm_decl.olean d) | failure
      return (olean_to_lean n)) <|>
    return "[current file]"

unsafe def pos_info (fn : Name) : vm Stringₓ :=
  (do
      let d ← vm.get_decl fn
      let some p ← return (vm_decl.pos d) | failure
      let file ← get_file fn
      return s! "{file }:{p }:{p}") <|>
    return "<position not available>"

unsafe def show_fn (header : Stringₓ) (fn : Name) (frame : Nat) : vm Unit := do
  let pos ← pos_info fn
  vm.put_str s! "[{frame }] {header}"
  if header = "" then return () else vm.put_str " "
  vm.put_str
      s! "{fn } at {Pos}
        "

unsafe def show_curr_fn (header : Stringₓ) : vm Unit := do
  let fn ← vm.curr_fn
  let sz ← vm.call_stack_size
  show_fn header fn (sz - 1)

unsafe def is_valid_fn_prefix (p : Name) : vm Bool := do
  let env ← vm.get_env
  return <|
      env ff fun d r =>
        r ||
          let n := d
          p n

unsafe def show_frame (frame_idx : Nat) : vm Unit := do
  let sz ← vm.call_stack_size
  let fn ← if frame_idx ≥ sz then vm.curr_fn else vm.call_stack_fn frame_idx
  show_fn "" fn frame_idx

unsafe def type_to_string : Option expr → Nat → vm Stringₓ
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

unsafe def show_vars (frame : Nat) : vm Unit := do
  let (s, e) ← vm.call_stack_var_range frame
  show_vars_core 0 s e

unsafe def show_stack_core : Nat → vm Unit
  | 0 => return ()
  | i + 1 => do
    let fn ← vm.call_stack_fn i
    show_fn "" fn i
    show_stack_core i

unsafe def show_stack : vm Unit := do
  let sz ← vm.call_stack_size
  show_stack_core sz

end Debugger

