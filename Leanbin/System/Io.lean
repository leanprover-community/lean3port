import Leanbin.System.IoInterface

axiom IoCore : Type → Type → Type

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

def iterate {e α} (a : α) (f : α → IoCore e (Option α)) : IoCore e α :=
  MonadIo.iterate e α a f

def forever {e} (a : IoCore e Unit) : IoCore e Unit :=
  iterate () $ fun _ => a >> return (some ())

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

def put_str : Stringₓ → Io Unit :=
  MonadIoTerminal.putStr

def put_str_ln (s : Stringₓ) : Io Unit :=
  put_str s >> put_str "\n"

def get_line : Io Stringₓ :=
  MonadIoTerminal.getLine

def cmdline_args : Io (List Stringₓ) :=
  return (MonadIoTerminal.cmdlineArgs IoCore)

def print {α} [HasToString α] (s : α) : Io Unit :=
  put_str ∘ toString $ s

def print_ln {α} [HasToString α] (s : α) : Io Unit :=
  print s >> put_str "\n"

def handle : Type :=
  MonadIo.Handle IoCore

def mk_file_handle (s : Stringₓ) (m : mode) (bin : Bool := ff) : Io handle :=
  MonadIoFileSystem.mkFileHandle s m bin

def stdin : Io handle :=
  MonadIoFileSystem.stdin

def stderr : Io handle :=
  MonadIoFileSystem.stderr

def stdout : Io handle :=
  MonadIoFileSystem.stdout

unsafe def serialize : handle → expr → Io Unit :=
  monad_io_serial.serialize

unsafe def deserialize : handle → Io expr :=
  monad_io_serial.deserialize

namespace Env

def get (env_var : Stringₓ) : Io (Option Stringₓ) :=
  MonadIoEnvironment.getEnv env_var

/-- get the current working directory -/
def get_cwd : Io Stringₓ :=
  MonadIoEnvironment.getCwd

/-- set the current working directory -/
def set_cwd (cwd : Stringₓ) : Io Unit :=
  MonadIoEnvironment.setCwd cwd

end Env

namespace Net

def socket : Type :=
  MonadIoNetSystem.Socket IoCore

def listen : Stringₓ → Nat → Io socket :=
  MonadIoNetSystem.listen

def accept : socket → Io socket :=
  MonadIoNetSystem.accept

def connect : Stringₓ → Io socket :=
  MonadIoNetSystem.connect

def recv : socket → Nat → Io CharBuffer :=
  MonadIoNetSystem.recv

def send : socket → CharBuffer → Io Unit :=
  MonadIoNetSystem.send

def close : socket → Io Unit :=
  MonadIoNetSystem.close

end Net

namespace Fs

def is_eof : handle → Io Bool :=
  MonadIoFileSystem.isEof

def flush : handle → Io Unit :=
  MonadIoFileSystem.flush

def close : handle → Io Unit :=
  MonadIoFileSystem.close

def read : handle → Nat → Io CharBuffer :=
  MonadIoFileSystem.read

def write : handle → CharBuffer → Io Unit :=
  MonadIoFileSystem.write

def get_char (h : handle) : Io Charₓ := do
  let b ← read h 1
  if h : b.size = 1 then return $ b.read ⟨0, h.symm ▸ Nat.zero_lt_oneₓ⟩ else Io.fail "get_char failed"

def get_line : handle → Io CharBuffer :=
  MonadIoFileSystem.getLine

def put_char (h : handle) (c : Charₓ) : Io Unit :=
  write h (mkBuffer.pushBack c)

def put_str (h : handle) (s : Stringₓ) : Io Unit :=
  write h (mkBuffer.appendString s)

def put_str_ln (h : handle) (s : Stringₓ) : Io Unit :=
  put_str h s >> put_str h "\n"

def read_to_end (h : handle) : Io CharBuffer :=
  iterate mkBuffer $ fun r => do
    let done ← is_eof h
    if done then return none
      else do
        let c ← read h 1024
        return $ some (r ++ c)

def read_file (s : Stringₓ) (bin := ff) : Io CharBuffer := do
  let h ← mk_file_handle s Io.Mode.read bin
  read_to_end h

def file_exists : Stringₓ → Io Bool :=
  MonadIoFileSystem.fileExists

def dir_exists : Stringₓ → Io Bool :=
  MonadIoFileSystem.dirExists

def remove : Stringₓ → Io Unit :=
  MonadIoFileSystem.remove

def rename : Stringₓ → Stringₓ → Io Unit :=
  MonadIoFileSystem.rename

def mkdir (path : Stringₓ) (recursive : Bool := ff) : Io Bool :=
  MonadIoFileSystem.mkdir path recursive

def rmdir : Stringₓ → Io Bool :=
  MonadIoFileSystem.rmdir

end Fs

namespace Proc

def child : Type :=
  MonadIoProcess.Child IoCore

def child.stdin : child → handle :=
  MonadIoProcess.stdin

def child.stdout : child → handle :=
  MonadIoProcess.stdout

def child.stderr : child → handle :=
  MonadIoProcess.stderr

def spawn (p : Io.Process.SpawnArgs) : Io child :=
  MonadIoProcess.spawn p

def wait (c : child) : Io Nat :=
  MonadIoProcess.wait c

def sleep (n : Nat) : Io Unit :=
  MonadIoProcess.sleep n

end Proc

def set_rand_gen : StdGen → Io Unit :=
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
  Io.Fs.close child.stdout
  let exitv ← Io.Proc.wait child
  when (exitv ≠ 0) $ Io.fail $ "process exited with status " ++ reprₓ exitv
  return buf.to_string

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

