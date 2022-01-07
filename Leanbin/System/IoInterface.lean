import Leanbin.Data.Buffer
import Leanbin.System.Random

inductive Io.Error
  | other : Stringₓ → Io.Error
  | sys : Nat → Io.Error

inductive Io.Mode
  | read
  | write
  | read_write
  | append

inductive Io.Process.Stdio
  | piped
  | inherit
  | null

structure Io.Process.SpawnArgs where
  cmd : Stringₓ
  args : List Stringₓ := []
  stdin := stdio.inherit
  stdout := stdio.inherit
  stderr := stdio.inherit
  cwd : Option Stringₓ := none
  env : List (Stringₓ × Option Stringₓ) := []

class MonadIo (m : Type → Type → Type) where
  [Monad : ∀ e, Monadₓ (m e)]
  catch : ∀ e₁ e₂ α, m e₁ α → (e₁ → m e₂ α) → m e₂ α
  fail : ∀ e α, e → m e α
  iterate : ∀ e α, α → (α → m e (Option α)) → m e α
  Handle : Type

class MonadIoTerminal (m : Type → Type → Type) where
  putStr : Stringₓ → m Io.Error Unit
  getLine : m Io.Error Stringₓ
  cmdlineArgs : List Stringₓ

open monad_io (Handle)

class MonadIoNetSystem (m : Type → Type → Type) [MonadIo m] where
  Socket : Type
  listen : Stringₓ → Nat → m Io.Error socket
  accept : socket → m Io.Error socket
  connect : Stringₓ → m Io.Error socket
  recv : socket → Nat → m Io.Error CharBuffer
  send : socket → CharBuffer → m Io.Error Unit
  close : socket → m Io.Error Unit

class MonadIoFileSystem (m : Type → Type → Type) [MonadIo m] where
  mkFileHandle : Stringₓ → Io.Mode → Bool → m Io.Error (handle m)
  isEof : handle m → m Io.Error Bool
  flush : handle m → m Io.Error Unit
  close : handle m → m Io.Error Unit
  read : handle m → Nat → m Io.Error CharBuffer
  write : handle m → CharBuffer → m Io.Error Unit
  getLine : handle m → m Io.Error CharBuffer
  stdin : m Io.Error (handle m)
  stdout : m Io.Error (handle m)
  stderr : m Io.Error (handle m)
  fileExists : Stringₓ → m Io.Error Bool
  dirExists : Stringₓ → m Io.Error Bool
  remove : Stringₓ → m Io.Error Unit
  rename : Stringₓ → Stringₓ → m Io.Error Unit
  mkdir : Stringₓ → Bool → m Io.Error Bool
  rmdir : Stringₓ → m Io.Error Bool

unsafe class monad_io_serial (m : Type → Type → Type) [MonadIo m] where
  serialize : handle m → expr → m Io.Error Unit
  deserialize : handle m → m Io.Error expr

class MonadIoEnvironment (m : Type → Type → Type) where
  getEnv : Stringₓ → m Io.Error (Option Stringₓ)
  getCwd : m Io.Error Stringₓ
  setCwd : Stringₓ → m Io.Error Unit

class MonadIoProcess (m : Type → Type → Type) [MonadIo m] where
  Child : Type
  stdin : child → handle m
  stdout : child → handle m
  stderr : child → handle m
  spawn : Io.Process.SpawnArgs → m Io.Error child
  wait : child → m Io.Error Nat
  sleep : Nat → m Io.Error Unit

class MonadIoRandom (m : Type → Type → Type) where
  setRandGen : StdGen → m Io.Error Unit
  rand : Nat → Nat → m Io.Error Nat

instance monadIoIsMonad (m : Type → Type → Type) (e : Type) [MonadIo m] : Monadₓ (m e) :=
  MonadIo.monad e

instance monadIoIsMonadFail (m : Type → Type → Type) [MonadIo m] : MonadFail (m Io.Error) where
  fail := fun α s => MonadIo.fail _ _ (Io.Error.other s)

instance monadIoIsAlternative (m : Type → Type → Type) [MonadIo m] : Alternativeₓ (m Io.Error) where
  orelse := fun α a b => MonadIo.catch _ _ _ a fun _ => b
  failure := fun α => MonadIo.fail _ _ (Io.Error.other "failure")

