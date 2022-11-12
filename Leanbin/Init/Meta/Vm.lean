/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Control.Option
import Leanbin.Init.Meta.MkDecEqInstance

unsafe axiom vm_obj : Type
#align vm_obj vm_obj

inductive VmObjKind
  | simple
  | constructor
  | closure
  | native_closure
  | mpz
  | Name
  | level
  | expr
  | declaration
  | environment
  | tactic_state
  | format
  | options
  | other
  deriving DecidableEq
#align vm_obj_kind VmObjKind

namespace VmObj

unsafe axiom kind : vm_obj → VmObjKind
#align vm_obj.kind vm_obj.kind

/-- For simple and constructor vm_obj's, it returns the constructor tag/index.
   Return 0 otherwise. -/
unsafe axiom cidx : vm_obj → Nat
#align vm_obj.cidx vm_obj.cidx

/-- For closure vm_obj's, it returns the internal function index. -/
unsafe axiom fn_idx : vm_obj → Nat
#align vm_obj.fn_idx vm_obj.fn_idx

/-- For constructor vm_obj's, it returns the data stored in the object.
   For closure vm_obj's, it returns the local arguments captured by the closure. -/
unsafe axiom fields : vm_obj → List vm_obj
#align vm_obj.fields vm_obj.fields

/-- For simple and mpz vm_obj's -/
unsafe axiom to_nat : vm_obj → Nat
#align vm_obj.to_nat vm_obj.to_nat

/-- For name vm_obj's, it returns the name wrapped by the vm_obj. -/
unsafe axiom to_name : vm_obj → Name
#align vm_obj.to_name vm_obj.to_name

/-- For level vm_obj's, it returns the universe level wrapped by the vm_obj. -/
unsafe axiom to_level : vm_obj → level
#align vm_obj.to_level vm_obj.to_level

/-- For expr vm_obj's, it returns the expression wrapped by the vm_obj. -/
unsafe axiom to_expr : vm_obj → expr
#align vm_obj.to_expr vm_obj.to_expr

/-- For declaration vm_obj's, it returns the declaration wrapped by the vm_obj. -/
unsafe axiom to_declaration : vm_obj → declaration
#align vm_obj.to_declaration vm_obj.to_declaration

/-- For environment vm_obj's, it returns the environment wrapped by the vm_obj. -/
unsafe axiom to_environment : vm_obj → environment
#align vm_obj.to_environment vm_obj.to_environment

/-- For tactic_state vm_obj's, it returns the tactic_state object wrapped by the vm_obj. -/
unsafe axiom to_tactic_state : vm_obj → tactic_state
#align vm_obj.to_tactic_state vm_obj.to_tactic_state

/-- For format vm_obj's, it returns the format object wrapped by the vm_obj. -/
unsafe axiom to_format : vm_obj → format
#align vm_obj.to_format vm_obj.to_format

end VmObj

unsafe axiom vm_decl : Type
#align vm_decl vm_decl

inductive VmDeclKind
  | bytecode
  | builtin
  | cfun
#align vm_decl_kind VmDeclKind

/-- Information for local variables and arguments on the VM stack.
   Remark: type is only available if it is a closed term at compilation time. -/
unsafe structure vm_local_info where
  id : Name
  type : Option expr
#align vm_local_info vm_local_info

namespace VmDecl

unsafe axiom kind : vm_decl → VmDeclKind
#align vm_decl.kind vm_decl.kind

unsafe axiom to_name : vm_decl → Name
#align vm_decl.to_name vm_decl.to_name

/-- Internal function index associated with the given VM declaration. -/
unsafe axiom idx : vm_decl → Nat
#align vm_decl.idx vm_decl.idx

/-- Number of arguments needed to execute the given VM declaration. -/
unsafe axiom arity : vm_decl → Nat
#align vm_decl.arity vm_decl.arity

/-- Return source position if available -/
unsafe axiom pos : vm_decl → Option Pos
#align vm_decl.pos vm_decl.pos

/-- Return .olean file where the given VM declaration was imported from. -/
unsafe axiom olean : vm_decl → Option String
#align vm_decl.olean vm_decl.olean

/-- Return names .olean file where the given VM declaration was imported from. -/
unsafe axiom args_info : vm_decl → List vm_local_info
#align vm_decl.args_info vm_decl.args_info

/--
If the given declaration is overridden by another declaration using the vm_override attribute, then this returns the overriding declaration.-/
unsafe axiom override_idx : vm_decl → Option Nat
#align vm_decl.override_idx vm_decl.override_idx

end VmDecl

unsafe axiom vm_core : Type → Type
#align vm_core vm_core

unsafe axiom vm_core.map {α β : Type} : (α → β) → vm_core α → vm_core β
#align vm_core.map vm_core.map

unsafe axiom vm_core.ret {α : Type} : α → vm_core α
#align vm_core.ret vm_core.ret

unsafe axiom vm_core.bind {α β : Type} : vm_core α → (α → vm_core β) → vm_core β
#align vm_core.bind vm_core.bind

unsafe instance : Monad vm_core where
  map := @vm_core.map
  pure := @vm_core.ret
  bind := @vm_core.bind

@[reducible]
unsafe def vm (α : Type) : Type :=
  OptionT vm_core α
#align vm vm

namespace Vm

unsafe axiom get_env : vm environment
#align vm.get_env vm.get_env

/-- Returns the vm declaration associated with the given name. Remark: does _not_ return the vm_override if present.-/
unsafe axiom get_decl : Name → vm vm_decl
#align vm.get_decl vm.get_decl

/-- Returns the vm declaration associated with the given index. Remark: does _not_ return the vm_override if present.-/
unsafe axiom decl_of_idx : Nat → vm vm_decl
#align vm.decl_of_idx vm.decl_of_idx

unsafe def get_override : vm_decl → vm vm_decl
  | d => OptionT.ofOption d.override_idx >>= decl_of_idx
#align vm.get_override vm.get_override

unsafe axiom get_options : vm options
#align vm.get_options vm.get_options

unsafe axiom stack_size : vm Nat
#align vm.stack_size vm.stack_size

/-- Return the vm_obj stored at the given position on the execution stack.
   It fails if position >= vm.stack_size -/
unsafe axiom stack_obj : Nat → vm vm_obj
#align vm.stack_obj vm.stack_obj

/-- Return (name, type) for the object at the given position on the execution stack.
   It fails if position >= vm.stack_size.
   The name is anonymous if vm_obj is a transient value created by the compiler.
   Type information is only recorded if the type is a closed term at compilation time. -/
unsafe axiom stack_obj_info : Nat → vm (Name × Option expr)
#align vm.stack_obj_info vm.stack_obj_info

/-- Pretty print the vm_obj at the given position on the execution stack. -/
unsafe axiom pp_stack_obj : Nat → vm format
#align vm.pp_stack_obj vm.pp_stack_obj

/-- Pretty print the given expression. -/
unsafe axiom pp_expr : expr → vm format
#align vm.pp_expr vm.pp_expr

/-- Number of frames on the call stack. -/
unsafe axiom call_stack_size : vm Nat
#align vm.call_stack_size vm.call_stack_size

/-- Return the function name at the given stack frame.
   Action fails if position >= vm.call_stack_size. -/
unsafe axiom call_stack_fn : Nat → vm Name
#align vm.call_stack_fn vm.call_stack_fn

/-- Return the range [start, end) for the given stack frame.
   Action fails if position >= vm.call_stack_size.
   The values start and end correspond to positions at the execution stack.
   We have that 0 <= start < end <= vm.stack_size -/
unsafe axiom call_stack_var_range : Nat → vm (Nat × Nat)
#align vm.call_stack_var_range vm.call_stack_var_range

/-- Return the name of the function on top of the call stack. -/
unsafe axiom curr_fn : vm Name
#align vm.curr_fn vm.curr_fn

/-- Return the base stack pointer for the frame on top of the call stack. -/
unsafe axiom bp : vm Nat
#align vm.bp vm.bp

/-- Return the program counter. -/
unsafe axiom pc : vm Nat
#align vm.pc vm.pc

/-- Convert the given vm_obj into a string -/
unsafe axiom obj_to_string : vm_obj → vm String
#align vm.obj_to_string vm.obj_to_string

unsafe axiom put_str : String → vm Unit
#align vm.put_str vm.put_str

unsafe axiom get_line : vm String
#align vm.get_line vm.get_line

/-- Return tt if end of the input stream has been reached.
   For example, this can happen if the user presses Ctrl-D -/
unsafe axiom eof : vm Bool
#align vm.eof vm.eof

/-- Return the list of declarations tagged with the given attribute. -/
unsafe axiom get_attribute : Name → vm (List Name)
#align vm.get_attribute vm.get_attribute

unsafe def trace {α : Type} [has_to_format α] (a : α) : vm Unit := do
  let fmt ← return <| to_fmt a
  return <| _root_.trace_fmt fmt fun u => ()
#align vm.trace vm.trace

end Vm

/-- A Lean VM monitor. Monitors are registered using the [vm_monitor] attribute.

    If option 'debugger' is true, then the VM will initialize the vm_monitor state using the
    'init' field, and will invoke the function 'step' before each instruction is invoked. -/
unsafe structure vm_monitor (α : Type) where
  init : α
  step : α → vm α
#align vm_monitor vm_monitor

