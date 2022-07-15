/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Level
import Leanbin.Init.Control.Monad
import Leanbin.Init.Meta.RbMap

universe u v

open Native

/-- Column and line position in a Lean source file. -/
structure Pos where
  line : Nat
  column : Nat

instance : DecidableEq Pos
  | ⟨l₁, c₁⟩, ⟨l₂, c₂⟩ =>
    if h₁ : l₁ = l₂ then
      if h₂ : c₁ = c₂ then isTrue (Eq.recOnₓ h₁ (Eq.recOnₓ h₂ rfl))
      else isFalse fun contra => Pos.noConfusion contra fun e₁ e₂ => absurd e₂ h₂
    else isFalse fun contra => Pos.noConfusion contra fun e₁ e₂ => absurd e₁ h₁

unsafe instance : has_to_format Pos :=
  ⟨fun ⟨l, c⟩ => "⟨" ++ l ++ ", " ++ c ++ "⟩"⟩

/-- Auxiliary annotation for binders (Lambda and Pi).
    This information is only used for elaboration.
      The difference between `{}` and `⦃⦄` is how implicit arguments are treated that are *not* followed by explicit arguments.
  `{}` arguments are applied eagerly, while `⦃⦄` arguments are left partially applied:
```lean
def foo {x : ℕ} : ℕ := x
def bar ⦃x : ℕ⦄ : ℕ := x
#check foo -- foo : ℕ
#check bar -- bar : Π ⦃x : ℕ⦄, ℕ
```
    -/
inductive BinderInfo-- `(x : α)`

  | default-- `{x : α}`

  | implicit-- `⦃x:α⦄`

  | strict_implicit-- `[x : α]`. Should be inferred with typeclass resolution.

  | inst_implicit/- Auxiliary internal attribute used to mark local constants representing recursive functions
        in recursive equations and `match` statements. -/

  | aux_decl

instance : HasRepr BinderInfo :=
  ⟨fun bi =>
    match bi with
    | BinderInfo.default => "default"
    | BinderInfo.implicit => "implicit"
    | BinderInfo.strict_implicit => "strict_implicit"
    | BinderInfo.inst_implicit => "inst_implicit"
    | BinderInfo.aux_decl => "aux_decl"⟩

/-- Macros are basically "promises" to build an expr by some C++ code, you can't build them in Lean.
   You can unfold a macro and force it to evaluate.
   They are used for
   - `sorry`.
   - Term placeholders (`_`) in `pexpr`s.
   - Expression annotations. See `expr.is_annotation`.
   - Meta-recursive calls. Eg:
     ```
     meta def Y : (α → α) → α | f := f (Y f)
     ```
     The `Y` that appears in `f (Y f)` is a macro.
   - Builtin projections:
     ```
     structure foo := (mynat : ℕ)
     #print foo.mynat
     -- @[reducible]
     -- def foo.mynat : foo → ℕ :=
     -- λ (c : foo), [foo.mynat c]
     ```
     The thing in square brackets is a macro.
   - Ephemeral structures inside certain specialised C++ implemented tactics.
  -/
unsafe axiom macro_def : Type

/-- An expression. eg ```(4+5)```.

    The `elab` flag is indicates whether the `expr` has been elaborated and doesn't contain any placeholder macros.
    For example the equality `x = x` is represented in `expr ff` as ``app (app (const `eq _) x) x`` while in `expr tt` it is represented as ``app (app (app (const `eq _) t) x) x`` (one more argument).
    The VM replaces instances of this datatype with the C++ implementation. -/
unsafe inductive expr (elaborated : Bool := true)-- A bound variable with a de-Bruijn index.

  | var : Nat → expr-- A type universe: `Sort u`

  | sort : level → expr/- A global constant. These include definitions, constants and inductive type stuff present
in the environment as well as hard-coded definitions. -/

  | const : Name → List level → expr/- [WARNING] Do not trust the types for `mvar` and `local_const`,
they are sometimes dummy values. Use `tactic.infer_type` instead. -/
-- An `mvar` is a 'hole' yet to be filled in by the elaborator or tactic state.

  | mvar (unique : Name) (pretty : Name) (type : expr) :
    expr-- A local constant. For example, if our tactic state was `h : P ⊢ Q`, `h` would be a local constant.

  | local_const (unique : Name) (pretty : Name) (bi : BinderInfo) (type : expr) : expr-- Function application.

  | app : expr → expr → expr-- Lambda abstraction. eg ```(λ a : α, x)``

  | lam (var_name : Name) (bi : BinderInfo) (var_type : expr) (body : expr) :
    expr-- Pi type constructor. eg ```(Π a : α, x)`` and ```(α → β)``

  | pi (var_name : Name) (bi : BinderInfo) (var_type : expr) (body : expr) : expr-- An explicit let binding.

  | elet (var_name : Name) (type : expr) (assignment : expr) (body : expr) :
    expr/- A macro, see the docstring for `macro_def`.
  The list of expressions are local constants and metavariables that the macro depends on.
  -/

  | macro : macro_def → List expr → expr

variable {elab : Bool}

unsafe instance : Inhabited (expr elab) :=
  ⟨expr.sort level.zero⟩

/-- Get the name of the macro definition. -/
unsafe axiom expr.macro_def_name (d : macro_def) : Name

unsafe def expr.mk_var (n : Nat) : expr :=
  expr.var n

/-- Expressions can be annotated using an annotation macro during compilation.
For example, a `have x:X, from p, q` expression will be compiled to `(λ x:X,q)(p)`, but nested in an annotation macro with the name `"have"`.
These annotations have no real semantic meaning, but are useful for helping Lean's pretty printer. -/
unsafe axiom expr.is_annotation : expr elab → Option (Name × expr elab)

unsafe axiom expr.is_string_macro : expr elab → Option (expr elab)

/-- Remove all macro annotations from the given `expr`. -/
unsafe def expr.erase_annotations : expr elab → expr elab
  | e =>
    match e.is_annotation with
    | some (_, a) => expr.erase_annotations a
    | none => e

/-- Compares expressions, including binder names. -/
unsafe axiom expr.has_decidable_eq : DecidableEq expr

attribute [instance] expr.has_decidable_eq

/-- Compares expressions while ignoring binder names. -/
unsafe axiom expr.alpha_eqv : expr → expr → Bool

protected unsafe axiom expr.to_string : expr elab → Stringₓ

unsafe instance : HasToString (expr elab) :=
  ⟨expr.to_string⟩

unsafe instance : has_to_format (expr elab) :=
  ⟨fun e => e.toString⟩

/-- Coercion for letting users write (f a) instead of (expr.app f a) -/
unsafe instance : CoeFun (expr elab) fun e => expr elab → expr elab :=
  ⟨fun e => expr.app e⟩

/-- Each expression created by Lean carries a hash.
This is calculated upon creation of the expression.
Two structurally equal expressions will have the same hash. -/
unsafe axiom expr.hash : expr → Nat

/-- Compares expressions, ignoring binder names, and sorting by hash. -/
unsafe axiom expr.lt : expr → expr → Bool

/-- Compares expressions, ignoring binder names. -/
unsafe axiom expr.lex_lt : expr → expr → Bool

/-- `expr.fold e a f`: Traverses each subexpression of `e`. The `nat` passed to the folder `f` is the binder depth. -/
unsafe axiom expr.fold {α : Type} : expr → α → (expr → Nat → α → α) → α

/-- `expr.replace e f`
 Traverse over an expr `e` with a function `f` which can decide to replace subexpressions or not.
 For each subexpression `s` in the expression tree, `f s n` is called where `n` is how many binders are present above the given subexpression `s`.
 If `f s n` returns `none`, the children of `s` will be traversed.
 Otherwise if `some s'` is returned, `s'` will replace `s` and this subexpression will not be traversed further.
 -/
unsafe axiom expr.replace : expr → (expr → Nat → Option expr) → expr

/--
`abstract_local e n` replaces each instance of the local constant with unique (not pretty) name `n` in `e` with a de-Bruijn variable. -/
unsafe axiom expr.abstract_local : expr → Name → expr

/--
Multi version of `abstract_local`. Note that the given expression will only be traversed once, so this is not the same as `list.foldl expr.abstract_local`.-/
unsafe axiom expr.abstract_locals : expr → List Name → expr

/-- `abstract e x` Abstracts the expression `e` over the local constant `x`.  -/
unsafe def expr.abstract : expr → expr → expr
  | e, expr.local_const n m bi t => e.abstract_local n
  | e, _ => e

/-- Expressions depend on `level`s, and these may depend on universe parameters which have names.
`instantiate_univ_params e [(n₁,l₁), ...]` will traverse `e` and replace any universe parameters with name `nᵢ` with the corresponding level `lᵢ`.  -/
unsafe axiom expr.instantiate_univ_params : expr → List (Name × level) → expr

/-- `instantiate_nth_var n a b` takes the `n`th de-Bruijn variable in `a` and replaces each occurrence with `b`. -/
unsafe axiom expr.instantiate_nth_var : Nat → expr → expr → expr

/-- `instantiate_var a b` takes the 0th de-Bruijn variable in `a` and replaces each occurrence with `b`. -/
unsafe axiom expr.instantiate_var : expr → expr → expr

/-- ``instantiate_vars `(#0 #1 #2) [x,y,z] = `(%%x %%y %%z)`` -/
unsafe axiom expr.instantiate_vars : expr → List expr → expr

/-- Same as `instantiate_vars` except lifts and shifts the vars by the given amount.
``instantiate_vars_core `(#0 #1 #2 #3) 0 [x,y] = `(x y #0 #1)``
``instantiate_vars_core `(#0 #1 #2 #3) 1 [x,y] = `(#0 x y #1)``
``instantiate_vars_core `(#0 #1 #2 #3) 2 [x,y] = `(#0 #1 x y)``
-/
unsafe axiom expr.instantiate_vars_core : expr → Nat → List expr → expr

/-- Perform beta-reduction if the left expression is a lambda, or construct an application otherwise.
That is: ``expr.subst `(λ x, %%Y) Z = Y[x/Z]``, and
``expr.subst X Z = X.app Z`` otherwise -/
protected unsafe axiom expr.subst : expr elab → expr elab → expr elab

/--
`get_free_var_range e` returns one plus the maximum de-Bruijn value in `e`. Eg `get_free_var_range `(#1 #0)` yields `2` -/
unsafe axiom expr.get_free_var_range : expr → Nat

/-- `has_var e` returns true iff e has free variables. -/
unsafe axiom expr.has_var : expr → Bool

/-- `has_var_idx e n` returns true iff `e` has a free variable with de-Bruijn index `n`. -/
unsafe axiom expr.has_var_idx : expr → Nat → Bool

/-- `has_local e` returns true if `e` contains a local constant. -/
unsafe axiom expr.has_local : expr → Bool

/-- `has_meta_var e` returns true iff `e` contains a metavariable. -/
unsafe axiom expr.has_meta_var : expr → Bool

/-- `lower_vars e s d` lowers the free variables >= s in `e` by `d`. Note that this can cause variable clashes.
    examples:
    -  ``lower_vars `(#2 #1 #0) 1 1 = `(#1 #0 #0)``
    -  ``lower_vars `(λ x, #2 #1 #0) 1 1 = `(λ x, #1 #1 #0 )``
    -/
unsafe axiom expr.lower_vars : expr → Nat → Nat → expr

/-- Lifts free variables. `lift_vars e s d` will lift all free variables with index `≥ s` in `e` by `d`. -/
unsafe axiom expr.lift_vars : expr → Nat → Nat → expr

/-- Get the position of the given expression in the Lean source file, if anywhere. -/
protected unsafe axiom expr.pos : expr elab → Option Pos

/-- `copy_pos_info src tgt` copies position information from `src` to `tgt`. -/
unsafe axiom expr.copy_pos_info : expr → expr → expr

/-- Returns `some n` when the given expression is a constant with the name `..._cnstr.n`
```
is_internal_cnstr : expr → option unsigned
|(const (mk_numeral n (mk_string "_cnstr" _)) _) := some n
|_ := none
```
[NOTE] This is not used anywhere in core Lean.
-/
unsafe axiom expr.is_internal_cnstr : expr → Option Unsigned

/-- There is a macro called a "nat_value_macro" holding a natural number which are used during compilation.
This function extracts that to a natural number. [NOTE] This is not used anywhere in Lean. -/
unsafe axiom expr.get_nat_value : expr → Option Nat

/-- Get a list of all of the universe parameters that the given expression depends on. -/
unsafe axiom expr.collect_univ_params : expr → List Name

/--
`occurs e t` returns `tt` iff `e` occurs in `t` up to α-equivalence. Purely structural: no unification or definitional equality. -/
unsafe axiom expr.occurs : expr → expr → Bool

/-- Returns true if any of the names in the given `name_set` are present in the given `expr`. -/
unsafe axiom expr.has_local_in : expr → name_set → Bool

/-- Computes the number of sub-expressions (constant time). -/
unsafe axiom expr.get_weight : expr → ℕ

/-- Computes the maximum depth of the expression (constant time). -/
unsafe axiom expr.get_depth : expr → ℕ

/--
`mk_delayed_abstraction m ls` creates a delayed abstraction on the metavariable `m` with the unique names of the local constants `ls`.
    If `m` is not a metavariable then this is equivalent to `abstract_locals`.
 -/
unsafe axiom expr.mk_delayed_abstraction : expr → List Name → expr

/-- If the given expression is a delayed abstraction macro, return `some ls`
where `ls` is a list of unique names of locals that will be abstracted. -/
unsafe axiom expr.get_delayed_abstraction_locals : expr → Option (List Name)

/-- (reflected a) is a special opaque container for a closed `expr` representing `a`.
    It can only be obtained via type class inference, which will use the representation
    of `a` in the calling context. Local constants in the representation are replaced
    by nested inference of `reflected` instances.

    The quotation expression `` `(a) `` (outside of patterns) is equivalent to `reflect a`
    and thus can be used as an explicit way of inferring an instance of `reflected a`.
    
    Note that the `α` argument is explicit to prevent it being treated as reducible by typeclass
    inference, as this breaks `reflected` instances on type synonyms. -/
@[class]
unsafe def reflected (α : Sort u) : α → Type := fun _ => expr

@[inline]
unsafe def reflected.to_expr {α : Sort u} {a : α} : reflected _ a → expr :=
  id

/-- This is a more strongly-typed version of `expr.subst` that keeps track of the value being
reflected. To obtain a term of type `reflected _`, use `` (`(λ x y, foo x y).subst ex).subst ey`` instead of
using `` `(foo %%ex %%ey) `` (which returns an `expr`). -/
@[inline]
unsafe def reflected.subst {α : Sort v} {β : α → Sort u} {f : ∀ a : α, β a} {a : α} :
    reflected _ f → reflected _ a → reflected _ (f a) :=
  expr.subst

@[instance]
protected unsafe axiom expr.reflect (e : expr elab) : reflected _ e

@[instance]
protected unsafe axiom string.reflect (s : Stringₓ) : reflected _ s

@[inline]
unsafe instance {α : Sort u} (a : α) : Coe (reflected _ a) expr :=
  ⟨reflected.to_expr⟩

protected unsafe def reflect {α : Sort u} (a : α) [h : reflected _ a] : reflected _ a :=
  h

unsafe instance {α} (a : α) : has_to_format (reflected _ a) :=
  ⟨fun h => to_fmt h.to_expr⟩

namespace Expr

open Decidable

unsafe def lt_prop (a b : expr) : Prop :=
  expr.lt a b = tt

unsafe instance : DecidableRel expr.lt_prop := fun a b => Bool.decidableEq _ _

/-- Compares expressions, ignoring binder names, and sorting by hash. -/
unsafe instance : LT expr :=
  ⟨expr.lt_prop⟩

unsafe def mk_true : expr :=
  const `true []

unsafe def mk_false : expr :=
  const `false []

/-- Returns the sorry macro with the given type. -/
unsafe axiom mk_sorry (type : expr) : expr

/-- Checks whether e is sorry, and returns its type. -/
unsafe axiom is_sorry (e : expr) : Option expr

/-- Replace each instance of the local constant with name `n` by the expression `s` in `e`. -/
unsafe def instantiate_local (n : Name) (s : expr) (e : expr) : expr :=
  instantiate_var (abstract_local e n) s

unsafe def instantiate_locals (s : List (Name × expr)) (e : expr) : expr :=
  instantiate_vars (abstract_locals e (List.reverse (List.map Prod.fst s))) (List.map Prod.snd s)

unsafe def is_var : expr → Bool
  | var _ => true
  | _ => false

unsafe def app_of_list : expr → List expr → expr
  | f, [] => f
  | f, p :: ps => app_of_list (f p) ps

unsafe def is_app : expr → Bool
  | app f a => true
  | e => false

unsafe def app_fn : expr → expr
  | app f a => f
  | a => a

unsafe def app_arg : expr → expr
  | app f a => a
  | a => a

unsafe def get_app_fn : expr elab → expr elab
  | app f a => get_app_fn f
  | a => a

unsafe def get_app_num_args : expr → Nat
  | app f a => get_app_num_args f + 1
  | e => 0

unsafe def get_app_args_aux : List expr → expr → List expr
  | r, app f a => get_app_args_aux (a :: r) f
  | r, e => r

unsafe def get_app_args : expr → List expr :=
  get_app_args_aux []

unsafe def mk_app : expr → List expr → expr
  | e, [] => e
  | e, x :: xs => mk_app (e x) xs

unsafe def mk_binding (ctor : Name → BinderInfo → expr → expr → expr) (e : expr) : ∀ l : expr, expr
  | local_const n pp_n bi ty => ctor pp_n bi ty (e.abstract_local n)
  | _ => e

/-- (bind_pi e l) abstracts and pi-binds the local `l` in `e` -/
unsafe def bind_pi :=
  mk_binding pi

/-- (bind_lambda e l) abstracts and lambda-binds the local `l` in `e` -/
unsafe def bind_lambda :=
  mk_binding lam

unsafe def ith_arg_aux : expr → Nat → expr
  | app f a, 0 => a
  | app f a, n + 1 => ith_arg_aux f n
  | e, _ => e

unsafe def ith_arg (e : expr) (i : Nat) : expr :=
  ith_arg_aux e (get_app_num_args e - i - 1)

unsafe def const_name : expr elab → Name
  | const n ls => n
  | e => Name.anonymous

unsafe def is_constant : expr elab → Bool
  | const n ls => true
  | e => false

unsafe def is_local_constant : expr → Bool
  | local_const n m bi t => true
  | e => false

unsafe def local_uniq_name : expr → Name
  | local_const n m bi t => n
  | e => Name.anonymous

unsafe def local_pp_name : expr elab → Name
  | local_const x n bi t => n
  | e => Name.anonymous

unsafe def local_type : expr elab → expr elab
  | local_const _ _ _ t => t
  | e => e

unsafe def is_aux_decl : expr → Bool
  | local_const _ _ BinderInfo.aux_decl _ => true
  | _ => false

unsafe def is_constant_of : expr elab → Name → Bool
  | const n₁ ls, n₂ => n₁ = n₂
  | e, n => false

unsafe def is_app_of (e : expr) (n : Name) : Bool :=
  is_constant_of (get_app_fn e) n

/-- The same as `is_app_of` but must also have exactly `n` arguments. -/
unsafe def is_napp_of (e : expr) (c : Name) (n : Nat) : Bool :=
  is_app_of e c ∧ get_app_num_args e = n

unsafe def is_false : expr → Bool
  | quote.1 False => true
  | _ => false

unsafe def is_not : expr → Option expr
  | quote.1 (Not (%%ₓa)) => some a
  | quote.1 ((%%ₓa) → False) => some a
  | e => none

unsafe def is_and : expr → Option (expr × expr)
  | quote.1 (And (%%ₓα) (%%ₓβ)) => some (α, β)
  | _ => none

unsafe def is_or : expr → Option (expr × expr)
  | quote.1 (Or (%%ₓα) (%%ₓβ)) => some (α, β)
  | _ => none

unsafe def is_iff : expr → Option (expr × expr)
  | quote.1 ((%%ₓa : Prop) ↔ %%ₓb) => some (a, b)
  | _ => none

unsafe def is_eq : expr → Option (expr × expr)
  | quote.1 ((%%ₓa : %%ₓ_) = %%ₓb) => some (a, b)
  | _ => none

unsafe def is_ne : expr → Option (expr × expr)
  | quote.1 ((%%ₓa : %%ₓ_) ≠ %%ₓb) => some (a, b)
  | _ => none

unsafe def is_bin_arith_app (e : expr) (op : Name) : Option (expr × expr) :=
  if is_napp_of e op 4 then some (app_arg (app_fn e), app_arg e) else none

unsafe def is_lt (e : expr) : Option (expr × expr) :=
  is_bin_arith_app e `` LT.lt

unsafe def is_gt (e : expr) : Option (expr × expr) :=
  is_bin_arith_app e `` Gt

unsafe def is_le (e : expr) : Option (expr × expr) :=
  is_bin_arith_app e `` LE.le

unsafe def is_ge (e : expr) : Option (expr × expr) :=
  is_bin_arith_app e `` Ge

unsafe def is_heq : expr → Option (expr × expr × expr × expr)
  | quote.1 (@HEq (%%ₓα) (%%ₓa) (%%ₓβ) (%%ₓb)) => some (α, a, β, b)
  | _ => none

unsafe def is_lambda : expr → Bool
  | lam _ _ _ _ => true
  | e => false

unsafe def is_pi : expr → Bool
  | pi _ _ _ _ => true
  | e => false

unsafe def is_arrow : expr → Bool
  | pi _ _ _ b => bnot (has_var b)
  | e => false

unsafe def is_let : expr → Bool
  | elet _ _ _ _ => true
  | e => false

/-- The name of the bound variable in a pi, lambda or let expression. -/
unsafe def binding_name : expr → Name
  | pi n _ _ _ => n
  | lam n _ _ _ => n
  | elet n _ _ _ => n
  | e => Name.anonymous

/-- The binder info of a pi or lambda expression. -/
unsafe def binding_info : expr → BinderInfo
  | pi _ bi _ _ => bi
  | lam _ bi _ _ => bi
  | e => BinderInfo.default

/-- The domain (type of bound variable) of a pi, lambda or let expression. -/
unsafe def binding_domain : expr → expr
  | pi _ _ d _ => d
  | lam _ _ d _ => d
  | elet _ d _ _ => d
  | e => e

/-- The body of a pi, lambda or let expression.
  This definition doesn't instantiate bound variables, and therefore produces a term that is open.
  See note [open expressions] in mathlib. -/
unsafe def binding_body : expr → expr
  | pi _ _ _ b => b
  | lam _ _ _ b => b
  | elet _ _ _ b => b
  | e => e

/-- `nth_binding_body n e` iterates `binding_body` `n` times to an iterated pi expression `e`.
  This definition doesn't instantiate bound variables, and therefore produces a term that is open.
  See note [open expressions] in mathlib. -/
unsafe def nth_binding_body : ℕ → expr → expr
  | n + 1, pi _ _ _ b => nth_binding_body n b
  | _, e => e

unsafe def is_macro : expr → Bool
  | macro d a => true
  | e => false

unsafe def is_numeral : expr → Bool
  | quote.1 (@Zero.zero (%%ₓα) (%%ₓs)) => true
  | quote.1 (@One.one (%%ₓα) (%%ₓs)) => true
  | quote.1 (@bit0 (%%ₓα) (%%ₓs) (%%ₓv)) => is_numeral v
  | quote.1 (@bit1 (%%ₓα) (%%ₓs₁) (%%ₓs₂) (%%ₓv)) => is_numeral v
  | _ => false

unsafe def pi_arity : expr → ℕ
  | pi _ _ _ b => pi_arity b + 1
  | _ => 0

unsafe def lam_arity : expr → ℕ
  | lam _ _ _ b => lam_arity b + 1
  | _ => 0

unsafe def imp (a b : expr) : expr :=
  pi `_ BinderInfo.default a b

/-- `lambdas cs e` lambda binds `e` with each of the local constants in `cs`.  -/
unsafe def lambdas : List expr → expr → expr
  | local_const uniq pp info t :: es, f => lam pp info t (abstract_local (lambdas es f) uniq)
  | _, f => f

/-- Same as `expr.lambdas` but with `pi`. -/
unsafe def pis : List expr → expr → expr
  | local_const uniq pp info t :: es, f => pi pp info t (abstract_local (pis es f) uniq)
  | _, f => f

unsafe def extract_opt_auto_param : expr → expr
  | quote.1 (@optParam (%%ₓt) _) => extract_opt_auto_param t
  | quote.1 (@AutoParam (%%ₓt) _) => extract_opt_auto_param t
  | e => e

open Format

private unsafe def p : List format → format
  | [] => ""
  | [x] => x.paren
  | x :: y :: xs => p ((x ++ format.line ++ y).group :: xs)

unsafe def to_raw_fmt : expr elab → format
  | var n => p ["var", to_fmt n]
  | sort l => p ["sort", to_fmt l]
  | const n ls => p ["const", to_fmt n, to_fmt ls]
  | mvar n m t => p ["mvar", to_fmt n, to_fmt m, to_raw_fmt t]
  | local_const n m bi t => p ["local_const", to_fmt n, to_fmt m, to_raw_fmt t]
  | app e f => p ["app", to_raw_fmt e, to_raw_fmt f]
  | lam n bi e t => p ["lam", to_fmt n, reprₓ bi, to_raw_fmt e, to_raw_fmt t]
  | pi n bi e t => p ["pi", to_fmt n, reprₓ bi, to_raw_fmt e, to_raw_fmt t]
  | elet n g e f => p ["elet", to_fmt n, to_raw_fmt g, to_raw_fmt e, to_raw_fmt f]
  | macro d args =>
    sbracket (format.join (List.intersperse " " ("macro" :: to_fmt (macro_def_name d) :: args.map to_raw_fmt)))

/-- Fold an accumulator `a` over each subexpression in the expression `e`.
The `nat` passed to `fn` is the number of binders above the subexpression. -/
unsafe def mfold {α : Type} {m : Type → Type} [Monadₓ m] (e : expr) (a : α) (fn : expr → Nat → α → m α) : m α :=
  fold e (return a) fun e n a => a >>= fn e n

end Expr

/-- An dictionary from `data` to expressions. -/
@[reducible]
unsafe def expr_map (data : Type) :=
  rb_map expr data

namespace ExprMap

export
  Native.RbMap (mk_core size Empty insert erase contains find min max fold keys values toList mfold of_list set_of_list map for filter)

unsafe def mk (data : Type) : expr_map data :=
  rb_map.mk expr data

end ExprMap

unsafe def mk_expr_map {data : Type} : expr_map data :=
  expr_map.mk data

@[reducible]
unsafe def expr_set :=
  rb_set expr

unsafe def mk_expr_set : expr_set :=
  mk_rb_set

