/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch and Leonardo de Moura
-/
import Leanbin.System.IoInterface

-- The following constants have a builtin implementation 
-- The following constants have a builtin implementation
axiom IoCore : Type → Type → Type

-- Auxiliary definition used in the builtin implementation of monad_io_random_impl
def ioRandNat : StdGen → Nat → Nat → Nat × StdGen :=
  randNatₓ

@[instance]
axiom monadIoImpl : MonadIo IoCore

@[instance]
axiom monadIoTerminalImpl : MonadIoTerminal IoCore

@[instance]
axiom monadIoNetSystemImpl : MonadIoNetSystem IoCore

@[instance]
axiom monadIoFileSystemImpl : MonadIoFileSystem IoCore

@[instance]
unsafe axiom monad_io_serial_impl : monad_io_serial IoCore

@[instance]
axiom monadIoEnvironmentImpl : MonadIoEnvironment IoCore

@[instance]
axiom monadIoProcessImpl : MonadIoProcess IoCore

@[instance]
axiom monadIoRandomImpl : MonadIoRandom IoCore

instance ioCoreIsMonad (e : Type) : Monadₓ (IoCore e) :=
  monadIoIsMonad IoCore e

instance ioCoreIsMonadFail : MonadFail (IoCore Io.Error) :=
  monadIoIsMonadFail IoCore

instance ioCoreIsAlternative : Alternativeₓ (IoCore Io.Error) :=
  monadIoIsAlternative IoCore

@[reducible]
def Io (α : Type) :=
  IoCore Io.Error α

namespace Io

/- Remark: the following definitions can be generalized and defined for any (m : Type -> Type -> Type)
   that implements the required type classes. However, the generalized versions are very inconvenient to use,
   (example: `#eval io.put_str "hello world"` does not work because we don't have enough information to infer `m`.).
-/
def iterate {e α} (a : α) (f : α → IoCore e (Option α)) : IoCore e α :=
  MonadIo.iterate e α a f

def forever {e} (a : IoCore e Unit) : IoCore e Unit :=
  (iterate ()) fun _ => a >> return (some ())

-- TODO(Leo): delete after we merge #1881
def catch {e₁ e₂ α} (a : IoCore e₁ α) (b : e₁ → IoCore e₂ α) : IoCore e₂ α :=
  MonadIo.catch e₁ e₂ α a b

def finally {α e} (a : IoCore e α) (cleanup : IoCore e Unit) : IoCore e α := do
  let res ← catch (Sum.inr <$> a) (return ∘ Sum.inl)
  cleanup
  match res with
    | Sum.inr res => return res
    | Sum.inl error => MonadIo.fail _ _ error

protected def fail {α : Type} (s : Stringₓ) : Io α :=
  MonadIo.fail _ _ (Io.Error.other s)

def putStr : Stringₓ → Io Unit :=
  MonadIoTerminal.putStr

def putStrLn (s : Stringₓ) : Io Unit :=
  putStr s >> putStr "\n"

def getLine : Io Stringₓ :=
  MonadIoTerminal.getLine

def cmdlineArgs : Io (List Stringₓ) :=
  return (MonadIoTerminal.cmdlineArgs IoCore)

def print {α} [HasToString α] (s : α) : Io Unit :=
  put_str ∘ toString <| s

def printLn {α} [HasToString α] (s : α) : Io Unit :=
  print s >> putStr "\n"

def Handle : Type :=
  MonadIo.Handle IoCore

def mkFileHandle (s : Stringₓ) (m : Mode) (bin : Bool := false) : Io Handle :=
  MonadIoFileSystem.mkFileHandle s m bin

def stdin : Io Handle :=
  MonadIoFileSystem.stdin

def stderr : Io Handle :=
  MonadIoFileSystem.stderr

def stdout : Io Handle :=
  MonadIoFileSystem.stdout

unsafe def serialize : Handle → expr → Io Unit :=
  monad_io_serial.serialize

unsafe def deserialize : Handle → Io expr :=
  monad_io_serial.deserialize

namespace Env

def get (env_var : Stringₓ) : Io (Option Stringₓ) :=
  MonadIoEnvironment.getEnv env_var

/-- get the current working directory -/
def getCwd : Io Stringₓ :=
  MonadIoEnvironment.getCwd

/-- set the current working directory -/
def setCwd (cwd : Stringₓ) : Io Unit :=
  MonadIoEnvironment.setCwd cwd

end Env

namespace Net

def Socket : Type :=
  MonadIoNetSystem.Socket IoCore

def listen : Stringₓ → Nat → Io Socket :=
  MonadIoNetSystem.listen

def accept : Socket → Io Socket :=
  MonadIoNetSystem.accept

def connect : Stringₓ → Io Socket :=
  MonadIoNetSystem.connect

def recv : Socket → Nat → Io CharBuffer :=
  MonadIoNetSystem.recv

def send : Socket → CharBuffer → Io Unit :=
  MonadIoNetSystem.send

def close : Socket → Io Unit :=
  MonadIoNetSystem.close

end Net

namespace Fs

def isEof : Handle → Io Bool :=
  MonadIoFileSystem.isEof

def flush : Handle → Io Unit :=
  MonadIoFileSystem.flush

def close : Handle → Io Unit :=
  MonadIoFileSystem.close

def read : Handle → Nat → Io CharBuffer :=
  MonadIoFileSystem.read

def write : Handle → CharBuffer → Io Unit :=
  MonadIoFileSystem.write

def getChar (h : Handle) : Io Charₓ := do
  let b ← read h 1
  if h : b = 1 then return <| b ⟨0, h ▸ Nat.zero_lt_oneₓ⟩ else Io.fail "get_char failed"

def getLine : Handle → Io CharBuffer :=
  MonadIoFileSystem.getLine

def putChar (h : Handle) (c : Charₓ) : Io Unit :=
  write h (mkBuffer.pushBack c)

def putStr (h : Handle) (s : Stringₓ) : Io Unit :=
  write h (mkBuffer.appendString s)

def putStrLn (h : Handle) (s : Stringₓ) : Io Unit :=
  putStr h s >> putStr h "\n"

def readToEnd (h : Handle) : Io CharBuffer :=
  (iterate mkBuffer) fun r => do
    let done ← isEof h
    if done then return none
      else do
        let c ← read h 1024
        return <| some (r ++ c)

def readFile (s : Stringₓ) (bin := false) : Io CharBuffer := do
  let h ← mkFileHandle s Io.Mode.read bin
  read_to_end h

def fileExists : Stringₓ → Io Bool :=
  MonadIoFileSystem.fileExists

def dirExists : Stringₓ → Io Bool :=
  MonadIoFileSystem.dirExists

def remove : Stringₓ → Io Unit :=
  MonadIoFileSystem.remove

def rename : Stringₓ → Stringₓ → Io Unit :=
  MonadIoFileSystem.rename

def mkdir (path : Stringₓ) (recursive : Bool := false) : Io Bool :=
  MonadIoFileSystem.mkdir path recursive

def rmdir : Stringₓ → Io Bool :=
  MonadIoFileSystem.rmdir

end Fs

namespace Proc

def Child : Type :=
  MonadIoProcess.Child IoCore

def Child.stdin : Child → Handle :=
  MonadIoProcess.stdin

def Child.stdout : Child → Handle :=
  MonadIoProcess.stdout

def Child.stderr : Child → Handle :=
  MonadIoProcess.stderr

def spawn (p : Io.Process.SpawnArgs) : Io Child :=
  MonadIoProcess.spawn p

def wait (c : Child) : Io Nat :=
  MonadIoProcess.wait c

def sleep (n : Nat) : Io Unit :=
  MonadIoProcess.sleep n

end Proc

def setRandGen : StdGen → Io Unit :=
  MonadIoRandom.setRandGen

def rand (lo : Nat := stdRange.1) (hi : Nat := stdRange.2) : Io Nat :=
  MonadIoRandom.rand lo hi

end Io

unsafe axiom format.print_using : format → options → Io Unit

unsafe def format.print (fmt : format) : Io Unit :=
  format.print_using fmt options.mk

unsafe def pp_using {α : Type} [has_to_format α] (a : α) (o : options) : Io Unit :=
  format.print_using (to_fmt a) o

unsafe def pp {α : Type} [has_to_format α] (a : α) : Io Unit :=
  format.print (to_fmt a)

/-- Run the external process specified by `args`.

    The process will run to completion with its output captured by a pipe, and
    read into `string` which is then returned. -/
def Io.cmd (args : Io.Process.SpawnArgs) : Io Stringₓ := do
  let child ← Io.Proc.spawn { args with stdout := Io.Process.Stdio.piped }
  let buf ← Io.Fs.readToEnd child.stdout
  Io.Fs.close child
  let exitv ← Io.Proc.wait child
  when (exitv ≠ 0) <| Io.fail <| "process exited with status " ++ reprₓ exitv
  return buf

/-- This is the "back door" into the `io` monad, allowing IO computation to be performed during tactic execution.
For this to be safe, the IO computation should be ideally free of side effects and independent of its environment.
This primitive is used to invoke external tools (e.g., SAT and SMT solvers) from a tactic.

IMPORTANT: this primitive can be used to implement `unsafe_perform_io {α : Type} : io α → option α`
or `unsafe_perform_io {α : Type} [inhabited α] : io α → α`. This can be accomplished by executing
the resulting tactic using an empty `tactic_state` (we have `tactic_state.mk_empty`).
If `unsafe_perform_io` is defined, and used to perform side-effects, users need to take the following
precautions:

- Use `@[noinline]` attribute in any function to invokes `tactic.unsafe_perform_io`.
  Reason: if the call is inlined, the IO may be performed more than once.

- Set `set_option compiler.cse false` before any function that invokes `tactic.unsafe_perform_io`.
  This option disables common subexpression elimination. Common subexpression elimination
  might combine two side effects that were meant to be separate.

TODO[Leo]: add `[noinline]` attribute and option `compiler.cse`.
-/
unsafe axiom tactic.unsafe_run_io {α : Type} : Io α → tactic α

/-- Execute the given tactic with a tactic_state object that contains:
   - The current environment in the virtual machine.
   - The current set of options in the virtual machine.
   - Empty metavariable and local contexts.
   - One single goal of the form `⊢ true`.
   This action is mainly useful for writing tactics that inspect
   the environment. -/
unsafe axiom io.run_tactic {α : Type} (a : tactic α) : Io α

