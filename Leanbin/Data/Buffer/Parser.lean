import Leanbin.Data.Buffer
import Leanbin.Data.Dlist

inductive ParseResult (α : Type)
  | done (pos : ℕ) (result : α) : ParseResult
  | fail (pos : ℕ) (expected : Dlist Stringₓ) : ParseResult

/-- The parser monad. If you are familiar with the Parsec library in Haskell, you will understand this.  -/
def Parser (α : Type) :=
  ∀ input : CharBuffer start : ℕ, ParseResult α

namespace Parser

variable {α β γ : Type}

protected def bind (p : Parser α) (f : α → Parser β) : Parser β := fun input pos =>
  match p input Pos with
  | ParseResult.done Pos a => f a input Pos
  | ParseResult.fail Pos expected => ParseResult.fail Pos expected

protected def pure (a : α) : Parser α := fun input pos => ParseResult.done Pos a

private theorem parser.id_map (p : Parser α) : Parser.bind p Parser.pure = p := by
  apply funext
  intro input
  apply funext
  intro pos
  dunfold Parser.bind
  cases p input Pos <;> exact rfl

private theorem parser.bind_assoc (p : Parser α) (q : α → Parser β) (r : β → Parser γ) :
    Parser.bind (Parser.bind p q) r = Parser.bind p fun a => Parser.bind (q a) r := by
  apply funext
  intro input
  apply funext
  intro pos
  dunfold Parser.bind
  cases p input Pos <;>
    try
      dunfold bind
  cases q result input pos_1 <;>
    try
      dunfold bind
  all_goals
    rfl

protected def fail (msg : Stringₓ) : Parser α := fun _ pos => ParseResult.fail Pos (Dlist.singleton msg)

instance : Monadₓ Parser where
  pure := @Parser.pure
  bind := @Parser.bind

instance : IsLawfulMonad Parser where
  id_map := @parser.id_map
  pure_bind := fun _ _ _ _ => rfl
  bind_assoc := @parser.bind_assoc

instance : MonadFail Parser :=
  { Parser.monad with fail := @Parser.fail }

protected def failure : Parser α := fun _ pos => ParseResult.fail Pos Dlist.empty

protected def orelse (p q : Parser α) : Parser α := fun input pos =>
  match p input Pos with
  | ParseResult.fail pos₁ expected₁ =>
    if pos₁ ≠ Pos then ParseResult.fail pos₁ expected₁
    else
      match q input Pos with
      | ParseResult.fail pos₂ expected₂ =>
        if pos₁ < pos₂ then ParseResult.fail pos₁ expected₁
        else if pos₂ < pos₁ then ParseResult.fail pos₂ expected₂ else ParseResult.fail pos₁ (expected₁ ++ expected₂)
      | ok => ok
  | ok => ok

instance : Alternativeₓ Parser where
  failure := @Parser.failure
  orelse := @Parser.orelse

instance : Inhabited (Parser α) :=
  ⟨Parser.failure⟩

/-- Overrides the expected token name, and does not consume input on failure. -/
def decorate_errors (msgs : Thunkₓ (List Stringₓ)) (p : Parser α) : Parser α := fun input pos =>
  match p input Pos with
  | ParseResult.fail _ expected => ParseResult.fail Pos (Dlist.lazyOfList (msgs ()))
  | ok => ok

/-- Overrides the expected token name, and does not consume input on failure. -/
def decorate_error (msg : Thunkₓ Stringₓ) (p : Parser α) : Parser α :=
  decorate_errors [msg ()] p

/-- Matches a single character. Fails only if there is no more input. -/
def any_char : Parser Charₓ := fun input pos =>
  if h : Pos < input.size then
    let c := input.read ⟨Pos, h⟩
    ParseResult.done (Pos + 1) c
  else ParseResult.fail Pos Dlist.empty

/-- Matches a single character satisfying the given predicate. -/
def sat (p : Charₓ → Prop) [DecidablePred p] : Parser Charₓ := fun input pos =>
  if h : Pos < input.size then
    let c := input.read ⟨Pos, h⟩
    if p c then ParseResult.done (Pos + 1) c else ParseResult.fail Pos Dlist.empty
  else ParseResult.fail Pos Dlist.empty

/-- Matches the empty word. -/
def eps : Parser Unit :=
  return ()

/-- Matches the given character. -/
def ch (c : Charₓ) : Parser Unit :=
  decorate_error c.to_string $ sat (· = c) >> eps

/-- Matches a whole char_buffer.  Does not consume input in case of failure. -/
def char_buf (s : CharBuffer) : Parser Unit :=
  decorate_error s.to_string $ s.to_list.mmap' ch

/-- Matches one out of a list of characters. -/
def one_of (cs : List Charₓ) : Parser Charₓ :=
  (decorate_errors do
      let c ← cs
      return c.to_string) $
    sat (· ∈ cs)

def one_of' (cs : List Charₓ) : Parser Unit :=
  one_of cs >> eps

/-- Matches a string.  Does not consume input in case of failure. -/
def str (s : Stringₓ) : Parser Unit :=
  decorate_error s $ s.to_list.mmap' ch

/-- Number of remaining input characters. -/
def remaining : Parser ℕ := fun input pos => ParseResult.done Pos (input.size - Pos)

/-- Matches the end of the input. -/
def eof : Parser Unit :=
  decorate_error "<end-of-file>" $ do
    let rem ← remaining
    guardₓ $ rem = 0

def foldr_core (f : α → β → β) (p : Parser α) (b : β) : ∀ reps : ℕ, Parser β
  | 0 => failure
  | reps + 1 =>
    (do
        let x ← p
        let xs ← foldr_core reps
        return (f x xs)) <|>
      return b

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldr (f : α → β → β) (p : Parser α) (b : β) : Parser β := fun input pos =>
  foldr_core f p b (input.size - Pos + 1) input Pos

def foldl_core (f : α → β → α) : ∀ a : α p : Parser β reps : ℕ, Parser α
  | a, p, 0 => failure
  | a, p, reps + 1 =>
    (do
        let x ← p
        foldl_core (f a x) p reps) <|>
      return a

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldl (f : α → β → α) (a : α) (p : Parser β) : Parser α := fun input pos =>
  foldl_core f a p (input.size - Pos + 1) input Pos

/-- Matches zero or more occurrences of `p`. -/
def many (p : Parser α) : Parser (List α) :=
  foldr List.cons p []

def many_char (p : Parser Charₓ) : Parser Stringₓ :=
  List.asStringₓ <$> many p

/-- Matches zero or more occurrences of `p`. -/
def many' (p : Parser α) : Parser Unit :=
  many p >> eps

/-- Matches one or more occurrences of `p`. -/
def many1 (p : Parser α) : Parser (List α) :=
  List.cons <$> p <*> many p

/-- Matches one or more occurences of the char parser `p` and implodes them into a string. -/
def many_char1 (p : Parser Charₓ) : Parser Stringₓ :=
  List.asStringₓ <$> many1 p

/-- Matches one or more occurrences of `p`, separated by `sep`. -/
def sep_by1 (sep : Parser Unit) (p : Parser α) : Parser (List α) :=
  List.cons <$> p <*> many (sep >> p)

/-- Matches zero or more occurrences of `p`, separated by `sep`. -/
def sep_by (sep : Parser Unit) (p : Parser α) : Parser (List α) :=
  sep_by1 sep p <|> return []

def fix_core (F : Parser α → Parser α) : ∀ max_depth : ℕ, Parser α
  | 0 => failure
  | max_depth + 1 => F (fix_core max_depth)

/-- Matches a digit (0-9). -/
def digit : Parser Nat :=
  decorate_error "<digit>" $ do
    let c ← sat fun c => '0' ≤ c ∧ c ≤ '9'
    pure $ c.to_nat - '0'.toNat

/-- Matches a natural number. Large numbers may cause performance issues, so
don't run this parser on untrusted input. -/
def Nat : Parser Nat :=
  decorate_error "<natural>" $ do
    let digits ← many1 digit
    pure $ Prod.fst $ digits.foldr (fun digit ⟨Sum, magnitude⟩ => ⟨Sum + digit * magnitude, magnitude * 10⟩) ⟨0, 1⟩

/-- Fixpoint combinator satisfying `fix F = F (fix F)`. -/
def fix (F : Parser α → Parser α) : Parser α := fun input pos => fix_core F (input.size - Pos + 1) input Pos

private def make_monospaced : Charₓ → Charₓ
  | '\n' => ' '
  | '\t' => ' '
  | '\x0d' => ' '
  | c => c

def mk_error_msg (input : CharBuffer) (pos : ℕ) (expected : Dlist Stringₓ) : CharBuffer :=
  let left_ctx := (input.take Pos).takeRight 10
  let right_ctx := (input.drop Pos).take 10
  (left_ctx.map make_monospaced ++ right_ctx.map make_monospaced ++ "\n".toCharBuffer ++ left_ctx.map fun _ => ' ') ++
            "^\n".toCharBuffer ++
          "\n".toCharBuffer ++
        "expected: ".toCharBuffer ++
      Stringₓ.toCharBuffer (" | ".intercalate expected.to_list) ++
    "\n".toCharBuffer

/-- Runs a parser on the given input.  The parser needs to match the complete input. -/
def run (p : Parser α) (input : CharBuffer) : Sum Stringₓ α :=
  match (p <* eof) input 0 with
  | ParseResult.done Pos res => Sum.inr res
  | ParseResult.fail Pos expected => Sum.inl $ Buffer.toString $ mk_error_msg input Pos expected

/-- Runs a parser on the given input.  The parser needs to match the complete input. -/
def run_string (p : Parser α) (input : Stringₓ) : Sum Stringₓ α :=
  run p input.to_char_buffer

end Parser

