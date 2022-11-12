/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Leanbin.Data.Buffer
import Leanbin.System.Random

inductive Io.Error
  | other : String → Io.Error
  | sys : Nat → Io.Error
#align io.error Io.Error

inductive Io.Mode
  | read
  | write
  | read_write
  | append
#align io.mode Io.Mode

inductive Io.Process.Stdio
  | piped
  | inherit
  | null
#align io.process.stdio Io.Process.Stdio

structure Io.Process.SpawnArgs where
  -- Command name.
  cmd : String
  -- Arguments for the process
  args : List String := []
  -- Configuration for the process' stdin handle.
  stdin := Stdio.inherit
  -- Configuration for the process' stdout handle.
  stdout := Stdio.inherit
  -- Configuration for the process' stderr handle.
  stderr := Stdio.inherit
  -- Working directory for the process.
  cwd : Option String := none
  -- Environment variables for the process.
  env : List (String × Option String) := []
#align io.process.spawn_args Io.Process.SpawnArgs

class MonadIo (m : Type → Type → Type) where
  [Monad : ∀ e, Monad (m e)]
  -- TODO(Leo): use monad_except after it is merged
  catch : ∀ e₁ e₂ α, m e₁ α → (e₁ → m e₂ α) → m e₂ α
  fail : ∀ e α, e → m e α
  iterate : ∀ e α, α → (α → m e (Option α)) → m e α
  -- Primitive Types
  Handle : Type
#align monad_io MonadIo

class MonadIoTerminal (m : Type → Type → Type) where
  putStr : String → m Io.Error Unit
  getLine : m Io.Error String
  cmdlineArgs : List String
#align monad_io_terminal MonadIoTerminal

open MonadIo (Handle)

class MonadIoNetSystem (m : Type → Type → Type) [MonadIo m] where
  Socket : Type
  listen : String → Nat → m Io.Error socket
  accept : socket → m Io.Error socket
  connect : String → m Io.Error socket
  recv : socket → Nat → m Io.Error CharBuffer
  send : socket → CharBuffer → m Io.Error Unit
  close : socket → m Io.Error Unit
#align monad_io_net_system MonadIoNetSystem

class MonadIoFileSystem (m : Type → Type → Type) [MonadIo m] where
  -- Remark: in Haskell, they also provide  (Maybe TextEncoding) and  NewlineMode
  mkFileHandle : String → Io.Mode → Bool → m Io.Error (Handle m)
  isEof : Handle m → m Io.Error Bool
  flush : Handle m → m Io.Error Unit
  close : Handle m → m Io.Error Unit
  read : Handle m → Nat → m Io.Error CharBuffer
  write : Handle m → CharBuffer → m Io.Error Unit
  getLine : Handle m → m Io.Error CharBuffer
  stdin : m Io.Error (Handle m)
  stdout : m Io.Error (Handle m)
  stderr : m Io.Error (Handle m)
  fileExists : String → m Io.Error Bool
  dirExists : String → m Io.Error Bool
  remove : String → m Io.Error Unit
  rename : String → String → m Io.Error Unit
  mkdir : String → Bool → m Io.Error Bool
  rmdir : String → m Io.Error Bool
#align monad_io_file_system MonadIoFileSystem

unsafe class monad_io_serial (m : Type → Type → Type) [MonadIo m] where
  serialize : Handle m → expr → m Io.Error Unit
  deserialize : Handle m → m Io.Error expr
#align monad_io_serial monad_io_serial

class MonadIoEnvironment (m : Type → Type → Type) where
  getEnv : String → m Io.Error (Option String)
  -- we don't provide set_env as it is (thread-)unsafe (at least with glibc)
  getCwd : m Io.Error String
  setCwd : String → m Io.Error Unit
#align monad_io_environment MonadIoEnvironment

class MonadIoProcess (m : Type → Type → Type) [MonadIo m] where
  Child : Type
  stdin : child → Handle m
  stdout : child → Handle m
  stderr : child → Handle m
  spawn : Io.Process.SpawnArgs → m Io.Error child
  wait : child → m Io.Error Nat
  sleep : Nat → m Io.Error Unit
#align monad_io_process MonadIoProcess

class MonadIoRandom (m : Type → Type → Type) where
  setRandGen : StdGen → m Io.Error Unit
  rand : Nat → Nat → m Io.Error Nat
#align monad_io_random MonadIoRandom

instance monadIoIsMonad (m : Type → Type → Type) (e : Type) [MonadIo m] : Monad (m e) :=
  MonadIo.monad e
#align monad_io_is_monad monadIoIsMonad

instance monadIoIsMonadFail (m : Type → Type → Type) [MonadIo m] :
    MonadFail (m Io.Error) where fail α s := MonadIo.fail _ _ (Io.Error.other s)
#align monad_io_is_monad_fail monadIoIsMonadFail

instance monadIoIsAlternative (m : Type → Type → Type) [MonadIo m] : Alternative (m Io.Error) where
  orelse α a b := MonadIo.catch _ _ _ a fun _ => b
  failure α := MonadIo.fail _ _ (Io.Error.other "failure")
#align monad_io_is_alternative monadIoIsAlternative

