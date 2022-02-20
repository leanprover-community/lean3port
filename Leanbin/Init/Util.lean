/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Format

universe u

/-- This function has a native implementation that tracks time. -/
def timeitₓ {α : Type u} (s : Stringₓ) (f : Thunkₓ α) : α :=
  f ()

/-- This function has a native implementation that displays the given string in the regular output stream. -/
def trace {α : Type u} (s : Stringₓ) (f : Thunkₓ α) : α :=
  f ()

unsafe def trace_val {α : Type u} [has_to_format α] (f : α) : α :=
  trace (to_fmt f).toString f

/-- This function has a native implementation that shows the VM call stack. -/
def traceCallStack {α : Type u} (f : Thunkₓ α) : α :=
  f ()

/-- This function has a native implementation that displays in the given position all trace messages used in f.
   The arguments line and col are filled by the elaborator. -/
def scopeTrace {α : Type u} {line col : Nat} (f : Thunkₓ α) : α :=
  f ()

/-- This function has a native implementation where
  the thunk is interrupted if it takes more than 'max' "heartbeats" to compute it.
  The heartbeat is approx. the maximum number of memory allocations (in thousands) performed by 'f ()'.
  This is a deterministic way of interrupting long running tasks. -/
unsafe def try_for {α : Type u} (max : Nat) (f : Thunkₓ α) : Option α :=
  some (f ())

/-- This function has a native implementation where
  the thunk is interrupted if it takes more than `max` milliseconds to compute it.
  This is useful due to the variance in the number of heartbeats used by tactics. -/
unsafe def try_for_time {α : Type u} (max : ℕ) (f : Thunkₓ α) : Option α :=
  some (f ())

/-- Throws an exception when it is evaluated.  -/
unsafe axiom undefined_core {α : Sort u} (message : Stringₓ) : α

unsafe def undefined {α : Sort u} : α :=
  undefined_core "undefined"

unsafe def unchecked_cast {α : Sort u} {β : Sort u} : α → β :=
  cast undefined

/-- For tactics to tag the proofs they construct.
  The tag is `unit` but is intended to be encoded by a constant, e.g.
  def tagged_proof.ring : unit := () -/
@[reducible]
def id_tag (tag : Unit) {p : Prop} (h : p) : p :=
  h

