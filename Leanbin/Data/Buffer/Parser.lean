/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Leanbin.Data.Buffer
import Leanbin.Data.Dlist

#align_import data.buffer.parser from "leanprover-community/lean"@"549e2fed50b361d0d49a3dd1e7ccb6de9440059b"

inductive ParseResult (α : Type)
  | done (pos : ℕ) (result : α) : ParseResult
  | fail (pos : ℕ) (expected : Std.DList String) : ParseResult
#align parse_result ParseResult

/--
The parser monad. If you are familiar with the Parsec library in Haskell, you will understand this.  -/
def Parser (α : Type) :=
  ∀ (input : CharBuffer) (start : ℕ), ParseResult α
#align parser Parser

namespace Parser

variable {α β γ : Type}

protected def bind (p : Parser α) (f : α → Parser β) : Parser β := fun input pos =>
  match p input Pos with
  | ParseResult.done Pos a => f a input Pos
  | ParseResult.fail Pos expected => ParseResult.fail Pos expected
#align parser.bind Parser.bind

protected def pure (a : α) : Parser α := fun input pos => ParseResult.done Pos a
#align parser.pure Parser.pure

private theorem parser.id_map (p : Parser α) : Parser.bind p Parser.pure = p :=
  by
  apply funext; intro input
  apply funext; intro pos
  dsimp only [Parser.bind]
  cases p input Pos <;> exact rfl

private theorem parser.bind_assoc (p : Parser α) (q : α → Parser β) (r : β → Parser γ) :
    Parser.bind (Parser.bind p q) r = Parser.bind p fun a => Parser.bind (q a) r :=
  by
  apply funext; intro input
  apply funext; intro pos
  dsimp only [Parser.bind]
  cases p input Pos <;> try dsimp only [bind]
  cases q result input pos_1 <;> try dsimp only [bind]
  all_goals rfl

protected def fail (msg : String) : Parser α := fun _ pos =>
  ParseResult.fail Pos (Std.DList.singleton msg)
#align parser.fail Parser.fail

instance : Monad Parser where
  pure := @Parser.pure
  bind := @Parser.bind

instance : LawfulMonad Parser where
  id_map := @Parser.id_map
  pure_bind _ _ _ _ := rfl
  bind_assoc := @Parser.bind_assoc

instance : MonadFail Parser :=
  { Parser.monad with fail := @Parser.fail }

protected def failure : Parser α := fun _ pos => ParseResult.fail Pos Std.DList.empty
#align parser.failure Parser.failure

protected def orelse (p q : Parser α) : Parser α := fun input pos =>
  match p input Pos with
  | ParseResult.fail pos₁ expected₁ =>
    if pos₁ ≠ Pos then ParseResult.fail pos₁ expected₁
    else
      match q input Pos with
      | ParseResult.fail pos₂ expected₂ =>
        if pos₁ < pos₂ then ParseResult.fail pos₁ expected₁
        else
          if pos₂ < pos₁ then ParseResult.fail pos₂ expected₂
          else-- pos₁ = pos₂
              ParseResult.fail
              pos₁ (expected₁ ++ expected₂)
      | ok => ok
  | ok => ok
#align parser.orelse Parser.orelse

instance : Alternative Parser where
  failure := @Parser.failure
  orelse := @Parser.orelse

instance : Inhabited (Parser α) :=
  ⟨Parser.failure⟩

/-- Overrides the expected token name, and does not consume input on failure. -/
def decorateErrors (msgs : Thunk (List String)) (p : Parser α) : Parser α := fun input pos =>
  match p input Pos with
  | ParseResult.fail _ expected => ParseResult.fail Pos (Std.DList.lazy_ofList (msgs ()))
  | ok => ok
#align parser.decorate_errors Parser.decorateErrors

/-- Overrides the expected token name, and does not consume input on failure. -/
def decorateError (msg : Thunk String) (p : Parser α) : Parser α :=
  decorateErrors [msg ()] p
#align parser.decorate_error Parser.decorateError

/-- Matches a single character. Fails only if there is no more input. -/
def anyChar : Parser Char := fun input pos =>
  if h : Pos < input.size then
    let c := input.read ⟨Pos, h⟩
    ParseResult.done (Pos + 1) c
  else ParseResult.fail Pos Std.DList.empty
#align parser.any_char Parser.anyChar

/-- Matches a single character satisfying the given predicate. -/
def sat (p : Char → Prop) [DecidablePred p] : Parser Char := fun input pos =>
  if h : Pos < input.size then
    let c := input.read ⟨Pos, h⟩
    if p c then ParseResult.done (Pos + 1) c else ParseResult.fail Pos Std.DList.empty
  else ParseResult.fail Pos Std.DList.empty
#align parser.sat Parser.sat

/-- Matches the empty word. -/
def eps : Parser Unit :=
  return ()
#align parser.eps Parser.eps

/-- Matches the given character. -/
def ch (c : Char) : Parser Unit :=
  decorateError c.toString <| sat (· = c) >> eps
#align parser.ch Parser.ch

/-- Matches a whole char_buffer.  Does not consume input in case of failure. -/
def charBuf (s : CharBuffer) : Parser Unit :=
  decorateError s.toString <| s.toList.mapM' ch
#align parser.char_buf Parser.charBuf

/-- Matches one out of a list of characters. -/
def oneOf (cs : List Char) : Parser Char :=
  (decorateErrors do
      let c ← cs
      return c) <|
    sat (· ∈ cs)
#align parser.one_of Parser.oneOf

def oneOf' (cs : List Char) : Parser Unit :=
  oneOf cs >> eps
#align parser.one_of' Parser.oneOf'

/-- Matches a string.  Does not consume input in case of failure. -/
def str (s : String) : Parser Unit :=
  decorateError s <| s.toList.mapM' ch
#align parser.str Parser.str

/-- Number of remaining input characters. -/
def remaining : Parser ℕ := fun input pos => ParseResult.done Pos (input.size - Pos)
#align parser.remaining Parser.remaining

/-- Matches the end of the input. -/
def eof : Parser Unit :=
  decorateError "<end-of-file>" do
    let rem ← remaining
    guard <| rem = 0
#align parser.eof Parser.eof

def foldrCore (f : α → β → β) (p : Parser α) (b : β) : ∀ reps : ℕ, Parser β
  | 0 => failure
  | reps + 1 =>
    (do
        let x ← p
        let xs ← foldr_core reps
        return (f x xs)) <|>
      return b
#align parser.foldr_core Parser.foldrCore

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldr (f : α → β → β) (p : Parser α) (b : β) : Parser β := fun input pos =>
  foldrCore f p b (input.size - Pos + 1) input Pos
#align parser.foldr Parser.foldr

def foldlCore (f : α → β → α) : ∀ (a : α) (p : Parser β) (reps : ℕ), Parser α
  | a, p, 0 => failure
  | a, p, reps + 1 =>
    (do
        let x ← p
        foldl_core (f a x) p reps) <|>
      return a
#align parser.foldl_core Parser.foldlCore

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldl (f : α → β → α) (a : α) (p : Parser β) : Parser α := fun input pos =>
  foldlCore f a p (input.size - Pos + 1) input Pos
#align parser.foldl Parser.foldl

/-- Matches zero or more occurrences of `p`. -/
def many (p : Parser α) : Parser (List α) :=
  foldr List.cons p []
#align parser.many Parser.many

def manyChar (p : Parser Char) : Parser String :=
  List.asString <$> many p
#align parser.many_char Parser.manyChar

/-- Matches zero or more occurrences of `p`. -/
def many' (p : Parser α) : Parser Unit :=
  many p >> eps
#align parser.many' Parser.many'

/-- Matches one or more occurrences of `p`. -/
def many1 (p : Parser α) : Parser (List α) :=
  List.cons <$> p <*> many p
#align parser.many1 Parser.many1

/-- Matches one or more occurences of the char parser `p` and implodes them into a string. -/
def manyChar1 (p : Parser Char) : Parser String :=
  List.asString <$> many1 p
#align parser.many_char1 Parser.manyChar1

/-- Matches one or more occurrences of `p`, separated by `sep`. -/
def sepBy1 (sep : Parser Unit) (p : Parser α) : Parser (List α) :=
  List.cons <$> p <*> many (sep >> p)
#align parser.sep_by1 Parser.sepBy1

/-- Matches zero or more occurrences of `p`, separated by `sep`. -/
def sepBy (sep : Parser Unit) (p : Parser α) : Parser (List α) :=
  sepBy1 sep p <|> return []
#align parser.sep_by Parser.sepBy

def fixCore (F : Parser α → Parser α) : ∀ max_depth : ℕ, Parser α
  | 0 => failure
  | max_depth + 1 => F (fix_core max_depth)
#align parser.fix_core Parser.fixCore

/-- Matches a digit (0-9). -/
def digit : Parser Nat :=
  decorateError "<digit>" do
    let c ← sat fun c => '0' ≤ c ∧ c ≤ '9'
    pure <| c - '0'.toNat
#align parser.digit Parser.digit

/-- Matches a natural number. Large numbers may cause performance issues, so
don't run this parser on untrusted input. -/
def nat : Parser Nat :=
  decorateError "<natural>" do
    let digits ← many1 digit
    pure <|
        Prod.fst <|
          digits (fun digit ⟨Sum, magnitude⟩ => ⟨Sum + digit * magnitude, magnitude * 10⟩) ⟨0, 1⟩
#align parser.nat Parser.nat

/-- Fixpoint combinator satisfying `fix F = F (fix F)`. -/
def fix (F : Parser α → Parser α) : Parser α := fun input pos =>
  fixCore F (input.size - Pos + 1) input Pos
#align parser.fix Parser.fix

private def make_monospaced : Char → Char
  | '\n' => ' '
  | '\t' => ' '
  | '\x0d' => ' '
  | c => c

def mkErrorMsg (input : CharBuffer) (pos : ℕ) (expected : Std.DList String) : CharBuffer :=
  let left_ctx := (input.take Pos).takeRight 10
  let right_ctx := (input.drop Pos).take 10
  (left_ctx.map makeMonospaced ++ right_ctx.map makeMonospaced ++ "\n".toCharBuffer ++
              left_ctx.map fun _ => ' ') ++
            "^\n".toCharBuffer ++
          "\n".toCharBuffer ++
        "expected: ".toCharBuffer ++
      String.toCharBuffer (" | ".intercalate expected.toList) ++
    "\n".toCharBuffer
#align parser.mk_error_msg Parser.mkErrorMsg

/-- Runs a parser on the given input.  The parser needs to match the complete input. -/
def run (p : Parser α) (input : CharBuffer) : Sum String α :=
  match (p <* eof) input 0 with
  | ParseResult.done Pos res => Sum.inr res
  | ParseResult.fail Pos expected => Sum.inl <| Buffer.toString <| mkErrorMsg input Pos expected
#align parser.run Parser.run

/-- Runs a parser on the given input.  The parser needs to match the complete input. -/
def runString (p : Parser α) (input : String) : Sum String α :=
  run p input.toCharBuffer
#align parser.run_string Parser.runString

end Parser

