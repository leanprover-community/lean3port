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

namespace VmObj

unsafe axiom kind : vm_obj → VmObjKind

/-- For simple and constructor vm_obj's, it returns the constructor tag/index.
   Return 0 otherwise. -/
unsafe axiom cidx : vm_obj → Nat

/-- For closure vm_obj's, it returns the internal function index. -/
unsafe axiom fn_idx : vm_obj → Nat

/-- For constructor vm_obj's, it returns the data stored in the object.
   For closure vm_obj's, it returns the local arguments captured by the closure. -/
unsafe axiom fields : vm_obj → List vm_obj

/-- For simple and mpz vm_obj's -/
unsafe axiom to_nat : vm_obj → Nat

/-- For name vm_obj's, it returns the name wrapped by the vm_obj. -/
unsafe axiom to_name : vm_obj → Name

/-- For level vm_obj's, it returns the universe level wrapped by the vm_obj. -/
unsafe axiom to_level : vm_obj → level

/-- For expr vm_obj's, it returns the expression wrapped by the vm_obj. -/
unsafe axiom to_expr : vm_obj → expr

/-- For declaration vm_obj's, it returns the declaration wrapped by the vm_obj. -/
unsafe axiom to_declaration : vm_obj → declaration

/-- For environment vm_obj's, it returns the environment wrapped by the vm_obj. -/
unsafe axiom to_environment : vm_obj → environment

/-- For tactic_state vm_obj's, it returns the tactic_state object wrapped by the vm_obj. -/
unsafe axiom to_tactic_state : vm_obj → tactic_state

/-- For format vm_obj's, it returns the format object wrapped by the vm_obj. -/
unsafe axiom to_format : vm_obj → format

end VmObj

unsafe axiom vm_decl : Type

inductive VmDeclKind
  | bytecode
  | builtin
  | cfun

/-- Information for local variables and arguments on the VM stack.
   Remark: type is only available if it is a closed term at compilation time. -/
unsafe structure vm_local_info where
  id : Name
  type : Option expr

namespace VmDecl

unsafe axiom kind : vm_decl → VmDeclKind

unsafe axiom to_name : vm_decl → Name

/-- Internal function index associated with the given VM declaration. -/
unsafe axiom idx : vm_decl → Nat

/-- Number of arguments needed to execute the given VM declaration. -/
unsafe axiom arity : vm_decl → Nat

/-- Return source position if available -/
unsafe axiom pos : vm_decl → Option Pos

/-- Return .olean file where the given VM declaration was imported from. -/
unsafe axiom olean : vm_decl → Option Stringₓ

/-- Return names .olean file where the given VM declaration was imported from. -/
unsafe axiom args_info : vm_decl → List vm_local_info

/--
If the given declaration is overridden by another declaration using the vm_override attribute, then this returns the overriding declaration.-/
unsafe axiom override_idx : vm_decl → Option Nat

end VmDecl

unsafe axiom vm_core : Type → Type

unsafe axiom vm_core.map {α β : Type} : (α → β) → vm_core α → vm_core β

unsafe axiom vm_core.ret {α : Type} : α → vm_core α

unsafe axiom vm_core.bind {α β : Type} : vm_core α → (α → vm_core β) → vm_core β

unsafe instance : Monadₓ vm_core where
  map := @vm_core.map
  pure := @vm_core.ret
  bind := @vm_core.bind

@[reducible]
unsafe def vm (α : Type) : Type :=
  OptionTₓ vm_core α

namespace Vm

unsafe axiom get_env : vm environment

/-- Returns the vm declaration associated with the given name. Remark: does _not_ return the vm_override if present.-/
unsafe axiom get_decl : Name → vm vm_decl

/-- Returns the vm declaration associated with the given index. Remark: does _not_ return the vm_override if present.-/
unsafe axiom decl_of_idx : Nat → vm vm_decl

unsafe def get_override : vm_decl → vm vm_decl
  | d => OptionTₓ.ofOption d.override_idx >>= decl_of_idx

unsafe axiom get_options : vm options

unsafe axiom stack_size : vm Nat

/-- Return the vm_obj stored at the given position on the execution stack.
   It fails if position >= vm.stack_size -/
unsafe axiom stack_obj : Nat → vm vm_obj

/-- Return (name, type) for the object at the given position on the execution stack.
   It fails if position >= vm.stack_size.
   The name is anonymous if vm_obj is a transient value created by the compiler.
   Type information is only recorded if the type is a closed term at compilation time. -/
unsafe axiom stack_obj_info : Nat → vm (Name × Option expr)

/-- Pretty print the vm_obj at the given position on the execution stack. -/
unsafe axiom pp_stack_obj : Nat → vm format

/-- Pretty print the given expression. -/
unsafe axiom pp_expr : expr → vm format

/-- Number of frames on the call stack. -/
unsafe axiom call_stack_size : vm Nat

/-- Return the function name at the given stack frame.
   Action fails if position >= vm.call_stack_size. -/
unsafe axiom call_stack_fn : Nat → vm Name

/-- Return the range [start, end) for the given stack frame.
   Action fails if position >= vm.call_stack_size.
   The values start and end correspond to positions at the execution stack.
   We have that 0 <= start < end <= vm.stack_size -/
unsafe axiom call_stack_var_range : Nat → vm (Nat × Nat)

/-- Return the name of the function on top of the call stack. -/
unsafe axiom curr_fn : vm Name

/-- Return the base stack pointer for the frame on top of the call stack. -/
unsafe axiom bp : vm Nat

/-- Return the program counter. -/
unsafe axiom pc : vm Nat

/-- Convert the given vm_obj into a string -/
unsafe axiom obj_to_string : vm_obj → vm Stringₓ

unsafe axiom put_str : Stringₓ → vm Unit

unsafe axiom get_line : vm Stringₓ

/-- Return tt if end of the input stream has been reached.
   For example, this can happen if the user presses Ctrl-D -/
unsafe axiom eof : vm Bool

/-- Return the list of declarations tagged with the given attribute. -/
unsafe axiom get_attribute : Name → vm (List Name)

unsafe def trace {α : Type} [has_to_format α] (a : α) : vm Unit := do
  let fmt ← return <| to_fmt a
  return <| _root_.trace_fmt fmt fun u => ()

end Vm

/-- A Lean VM monitor. Monitors are registered using the [vm_monitor] attribute.

    If option 'debugger' is true, then the VM will initialize the vm_monitor state using the
    'init' field, and will invoke the function 'step' before each instruction is invoked. -/
unsafe structure vm_monitor (α : Type) where
  init : α
  step : α → vm α

