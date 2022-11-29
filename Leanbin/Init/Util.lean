/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Format

universe u

/- warning: timeit -> timeit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}}, String -> (Thunkₓ.{u} α) -> α
but is expected to have type
  forall {α : Type}, ([mdata borrowed:1 String]) -> (IO α) -> (IO α)
Case conversion may be inaccurate. Consider using '#align timeit timeitₓ'. -/
/-- This function has a native implementation that tracks time. -/
def timeit {α : Type u} (s : String) (f : Thunk α) : α :=
  f ()
#align timeit timeit

/--
This function has a native implementation that displays the given string in the regular output stream. -/
def trace {α : Type u} (s : String) (f : Thunk α) : α :=
  f ()
#align trace trace

unsafe def trace_val {α : Type u} [has_to_format α] (f : α) : α :=
  trace (to_fmt f).toString f
#align trace_val trace_val

/-- This function has a native implementation that shows the VM call stack. -/
def traceCallStack {α : Type u} (f : Thunk α) : α :=
  f ()
#align trace_call_stack traceCallStack

/--
This function has a native implementation that displays in the given position all trace messages used in f.
   The arguments line and col are filled by the elaborator. -/
def scopeTrace {α : Type u} {line col : Nat} (f : Thunk α) : α :=
  f ()
#align scope_trace scopeTrace

/-- This function has a native implementation where
  the thunk is interrupted if it takes more than 'max' "heartbeats" to compute it.
  The heartbeat is approx. the maximum number of memory allocations (in thousands) performed by 'f ()'.
  This is a deterministic way of interrupting long running tasks. -/
unsafe def try_for {α : Type u} (max : Nat) (f : Thunk α) : Option α :=
  some (f ())
#align try_for try_for

/-- This function has a native implementation where
  the thunk is interrupted if it takes more than `max` milliseconds to compute it.
  This is useful due to the variance in the number of heartbeats used by tactics. -/
unsafe def try_for_time {α : Type u} (max : ℕ) (f : Thunk α) : Option α :=
  some (f ())
#align try_for_time try_for_time

/-- Throws an exception when it is evaluated.  -/
unsafe axiom undefined_core {α : Sort u} (message : String) : α
#align undefined_core undefined_core

unsafe def undefined {α : Sort u} : α :=
  undefined_core "undefined"
#align undefined undefined

unsafe def unchecked_cast {α : Sort u} {β : Sort u} : α → β :=
  cast undefined
#align unchecked_cast unchecked_cast

/-- For tactics to tag the proofs they construct.
  The tag is `unit` but is intended to be encoded by a constant, e.g.
  def tagged_proof.ring : unit := () -/
@[reducible]
def id_tag (tag : Unit) {p : Prop} (h : p) : p :=
  h
#align id_tag id_tag

