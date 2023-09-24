/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch and Leonardo de Moura
-/
import System.IoInterface

#align_import system.io from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

/-! The following constants have a builtin implementation -/


axiom IoCore : Type → Type → Type
#align io_core IoCore

/-- Auxiliary definition used in the builtin implementation of monad_io_random_impl -/
def ioRandNat : StdGen → Nat → Nat → Nat × StdGen :=
  randNat
#align io_rand_nat ioRandNat

@[instance]
axiom monadIoImpl : MonadIo IoCore
#align monad_io_impl monadIoImpl

@[instance]
axiom monadIoTerminalImpl : MonadIoTerminal IoCore
#align monad_io_terminal_impl monadIoTerminalImpl

@[instance]
axiom monadIoNetSystemImpl : MonadIoNetSystem IoCore
#align monad_io_net_system_impl monadIoNetSystemImpl

@[instance]
axiom monadIoFileSystemImpl : MonadIoFileSystem IoCore
#align monad_io_file_system_impl monadIoFileSystemImpl

@[instance]
unsafe axiom monad_io_serial_impl : monad_io_serial IoCore
#align monad_io_serial_impl monad_io_serial_impl

@[instance]
axiom monadIoEnvironmentImpl : MonadIoEnvironment IoCore
#align monad_io_environment_impl monadIoEnvironmentImpl

@[instance]
axiom monadIoProcessImpl : MonadIoProcess IoCore
#align monad_io_process_impl monadIoProcessImpl

@[instance]
axiom monadIoRandomImpl : MonadIoRandom IoCore
#align monad_io_random_impl monadIoRandomImpl

instance ioCoreIsMonad (e : Type) : Monad (IoCore e) :=
  monadIoIsMonad IoCore e
#align io_core_is_monad ioCoreIsMonad

instance ioCoreIsMonadFail : MonadFail (IoCore Io.Error) :=
  monadIoIsMonadFail IoCore
#align io_core_is_monad_fail ioCoreIsMonadFail

instance ioCoreIsAlternative : Alternative (IoCore Io.Error) :=
  monadIoIsAlternative IoCore
#align io_core_is_alternative ioCoreIsAlternative

@[reducible]
def Io (α : Type) :=
  IoCore Io.Error α
#align io Io

namespace Io

/-! Remark: the following definitions can be generalized and defined for any (m : Type -> Type -> Type)
   that implements the required type classes. However, the generalized versions are very inconvenient to use,
   (example: `#eval io.put_str "hello world"` does not work because we don't have enough information to infer `m`.).
-/


def iterate {e α} (a : α) (f : α → IoCore e (Option α)) : IoCore e α :=
  MonadIo.iterate e α a f
#align io.iterate Io.iterate

def forever {e} (a : IoCore e Unit) : IoCore e Unit :=
  iterate () fun _ => a >> return (some ())
#align io.forever Io.forever

-- TODO(Leo): delete after we merge #1881
def catch {e₁ e₂ α} (a : IoCore e₁ α) (b : e₁ → IoCore e₂ α) : IoCore e₂ α :=
  MonadIo.catch e₁ e₂ α a b
#align io.catch Io.catch

def finally {α e} (a : IoCore e α) (cleanup : IoCore e Unit) : IoCore e α := do
  let res ← catch (Sum.inr <$> a) (return ∘ Sum.inl)
  cleanup
  match res with
    | Sum.inr res => return res
    | Sum.inl error => MonadIo.fail _ _ error
#align io.finally Io.finally

protected def fail {α : Type} (s : String) : Io α :=
  MonadIo.fail _ _ (Io.Error.other s)
#align io.fail Io.fail

def putStr : String → Io Unit :=
  MonadIoTerminal.putStr
#align io.put_str Io.putStr

def putStrLn (s : String) : Io Unit :=
  putStr s >> putStr "\n"
#align io.put_str_ln Io.putStrLn

def getLine : Io String :=
  MonadIoTerminal.getLine
#align io.get_line Io.getLine

def cmdlineArgs : Io (List String) :=
  return (MonadIoTerminal.cmdlineArgs IoCore)
#align io.cmdline_args Io.cmdlineArgs

def print {α} [ToString α] (s : α) : Io Unit :=
  putStr ∘ toString <| s
#align io.print Io.print

def printLn {α} [ToString α] (s : α) : Io Unit :=
  print s >> putStr "\n"
#align io.print_ln Io.printLn

def Handle : Type :=
  MonadIo.Handle IoCore
#align io.handle Io.Handle

def mkFileHandle (s : String) (m : Mode) (bin : Bool := false) : Io Handle :=
  MonadIoFileSystem.mkFileHandle s m bin
#align io.mk_file_handle Io.mkFileHandle

def stdin : Io Handle :=
  MonadIoFileSystem.stdin
#align io.stdin Io.stdin

def stderr : Io Handle :=
  MonadIoFileSystem.stderr
#align io.stderr Io.stderr

def stdout : Io Handle :=
  MonadIoFileSystem.stdout
#align io.stdout Io.stdout

unsafe def serialize : Handle → expr → Io Unit :=
  monad_io_serial.serialize
#align io.serialize io.serialize

unsafe def deserialize : Handle → Io expr :=
  monad_io_serial.deserialize
#align io.deserialize io.deserialize

namespace Env

def get (env_var : String) : Io (Option String) :=
  MonadIoEnvironment.getEnv env_var
#align io.env.get Io.Env.get

/-- get the current working directory -/
def getCwd : Io String :=
  MonadIoEnvironment.getCwd
#align io.env.get_cwd Io.Env.getCwd

/-- set the current working directory -/
def setCwd (cwd : String) : Io Unit :=
  MonadIoEnvironment.setCwd cwd
#align io.env.set_cwd Io.Env.setCwd

end Env

namespace Net

def Socket : Type :=
  MonadIoNetSystem.Socket IoCore
#align io.net.socket Io.Net.Socket

def listen : String → Nat → Io Socket :=
  MonadIoNetSystem.listen
#align io.net.listen Io.Net.listen

def accept : Socket → Io Socket :=
  MonadIoNetSystem.accept
#align io.net.accept Io.Net.accept

def connect : String → Io Socket :=
  MonadIoNetSystem.connect
#align io.net.connect Io.Net.connect

def recv : Socket → Nat → Io CharBuffer :=
  MonadIoNetSystem.recv
#align io.net.recv Io.Net.recv

def send : Socket → CharBuffer → Io Unit :=
  MonadIoNetSystem.send
#align io.net.send Io.Net.send

def close : Socket → Io Unit :=
  MonadIoNetSystem.close
#align io.net.close Io.Net.close

end Net

namespace Fs

def isEof : Handle → Io Bool :=
  MonadIoFileSystem.isEof
#align io.fs.is_eof Io.Fs.isEof

def flush : Handle → Io Unit :=
  MonadIoFileSystem.flush
#align io.fs.flush Io.Fs.flush

def close : Handle → Io Unit :=
  MonadIoFileSystem.close
#align io.fs.close Io.Fs.close

def read : Handle → Nat → Io CharBuffer :=
  MonadIoFileSystem.read
#align io.fs.read Io.Fs.read

def write : Handle → CharBuffer → Io Unit :=
  MonadIoFileSystem.write
#align io.fs.write Io.Fs.write

def getChar (h : Handle) : Io Char := do
  let b ← read h 1
  if h : b = 1 then return <| b ⟨0, h ▸ Nat.zero_lt_one⟩ else Io.fail "get_char failed"
#align io.fs.get_char Io.Fs.getChar

def getLine : Handle → Io CharBuffer :=
  MonadIoFileSystem.getLine
#align io.fs.get_line Io.Fs.getLine

def putChar (h : Handle) (c : Char) : Io Unit :=
  write h (mkBuffer.pushBack c)
#align io.fs.put_char Io.Fs.putChar

def putStr (h : Handle) (s : String) : Io Unit :=
  write h (mkBuffer.appendString s)
#align io.fs.put_str Io.Fs.putStr

def putStrLn (h : Handle) (s : String) : Io Unit :=
  putStr h s >> putStr h "\n"
#align io.fs.put_str_ln Io.Fs.putStrLn

def readToEnd (h : Handle) : Io CharBuffer :=
  iterate mkBuffer fun r => do
    let done ← isEof h
    if done then return none
      else do
        let c ← read h 1024
        return <| some (r ++ c)
#align io.fs.read_to_end Io.Fs.readToEnd

def readFile (s : String) (bin := false) : Io CharBuffer := do
  let h ← mkFileHandle s Io.Mode.read bin
  read_to_end h
#align io.fs.read_file Io.Fs.readFile

def fileExists : String → Io Bool :=
  MonadIoFileSystem.fileExists
#align io.fs.file_exists Io.Fs.fileExists

def dirExists : String → Io Bool :=
  MonadIoFileSystem.dirExists
#align io.fs.dir_exists Io.Fs.dirExists

def remove : String → Io Unit :=
  MonadIoFileSystem.remove
#align io.fs.remove Io.Fs.remove

def rename : String → String → Io Unit :=
  MonadIoFileSystem.rename
#align io.fs.rename Io.Fs.rename

def mkdir (path : String) (recursive : Bool := false) : Io Bool :=
  MonadIoFileSystem.mkdir Path recursive
#align io.fs.mkdir Io.Fs.mkdir

def rmdir : String → Io Bool :=
  MonadIoFileSystem.rmdir
#align io.fs.rmdir Io.Fs.rmdir

end Fs

namespace Proc

def Child : Type :=
  MonadIoProcess.Child IoCore
#align io.proc.child Io.Proc.Child

def Child.stdin : Child → Handle :=
  MonadIoProcess.stdin
#align io.proc.child.stdin Io.Proc.Child.stdin

def Child.stdout : Child → Handle :=
  MonadIoProcess.stdout
#align io.proc.child.stdout Io.Proc.Child.stdout

def Child.stderr : Child → Handle :=
  MonadIoProcess.stderr
#align io.proc.child.stderr Io.Proc.Child.stderr

def spawn (p : Io.Process.SpawnArgs) : Io Child :=
  MonadIoProcess.spawn p
#align io.proc.spawn Io.Proc.spawn

def wait (c : Child) : Io Nat :=
  MonadIoProcess.wait c
#align io.proc.wait Io.Proc.wait

def sleep (n : Nat) : Io Unit :=
  MonadIoProcess.sleep n
#align io.proc.sleep Io.Proc.sleep

end Proc

def setRandGen : StdGen → Io Unit :=
  MonadIoRandom.setRandGen
#align io.set_rand_gen Io.setRandGen

def rand (lo : Nat := stdRange.1) (hi : Nat := stdRange.2) : Io Nat :=
  MonadIoRandom.rand lo hi
#align io.rand Io.rand

end Io

unsafe axiom format.print_using : format → options → Io Unit
#align format.print_using format.print_using

unsafe def format.print (fmt : format) : Io Unit :=
  format.print_using fmt options.mk
#align format.print format.print

unsafe def pp_using {α : Type} [has_to_format α] (a : α) (o : options) : Io Unit :=
  format.print_using (to_fmt a) o
#align pp_using pp_using

unsafe def pp {α : Type} [has_to_format α] (a : α) : Io Unit :=
  format.print (to_fmt a)
#align pp pp

/-- Run the external process specified by `args`.

    The process will run to completion with its output captured by a pipe, and
    read into `string` which is then returned. -/
def Io.cmd (args : Io.Process.SpawnArgs) : Io String := do
  let child ← Io.Proc.spawn { args with stdout := Io.Process.Stdio.piped }
  let buf ← Io.Fs.readToEnd child.stdout
  Io.Fs.close child
  let exitv ← Io.Proc.wait child
  when (exitv ≠ 0) <| Io.fail <| "process exited with status " ++ repr exitv
  return buf
#align io.cmd Io.cmd

/--
This is the "back door" into the `io` monad, allowing IO computation to be performed during tactic execution.
For this to be safe, the IO computation should be ideally free of side effects and independent of its environment.
This primitive is used to invoke external tools (e.g., SAT and SMT solvers) from a tactic.

-/
unsafe axiom tactic.unsafe_run_io {α : Type} : Io α → tactic α
#align tactic.unsafe_run_io tactic.unsafe_run_io

/-- Execute the given tactic with a tactic_state object that contains:
   - The current environment in the virtual machine.
   - The current set of options in the virtual machine.
   - Empty metavariable and local contexts.
   - One single goal of the form `⊢ true`.
   This action is mainly useful for writing tactics that inspect
   the environment. -/
unsafe axiom io.run_tactic {α : Type} (a : tactic α) : Io α
#align io.run_tactic io.run_tactic

/--
Similarly to `tactic.unsafe_run_io`, this gives an unsafe backdoor to run io inside a pure function.

If `unsafe_perform_io` is used to perform side-effects, users need to take the following
precautions:

- Use `@[noinline]` attribute in any function to invokes `tactic.unsafe_perform_io`.
  Reason: if the call is inlined, the IO may be performed more than once.

- Set `set_option compiler.cse false` before any function that invokes `tactic.unsafe_perform_io`.
  This option disables common subexpression elimination. Common subexpression elimination
  might combine two side effects that were meant to be separate.

TODO[Leo]: add `[noinline]` attribute and option `compiler.cse`.
-/
unsafe axiom io.unsafe_perform_io {α : Type} (a : Io α) : Except Io.Error α
#align io.unsafe_perform_io io.unsafe_perform_io

