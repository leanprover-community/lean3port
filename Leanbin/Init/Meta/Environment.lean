/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Declaration
import Leanbin.Init.Meta.Exceptional
import Leanbin.Init.Data.Option.Basic
import Leanbin.Init.Meta.RbMap

/-- An __environment__ contains all of the declarations and notation that have been defined so far.   -/
unsafe axiom environment : Type

namespace Environment

/-- Consider a type `ψ` which is an inductive datatype using a single constructor `mk (a : α) (b : β) : ψ`.
Lean will automatically make two projection functions `a : ψ → α`, `b : ψ → β`.
Lean tags these declarations as __projections__.
This helps the simplifier / rewriter not have to expand projectors.
Eg `a (mk x y)` will automatically reduce to `x`.
If you `extend` a structure, all of the projections on the parent will also be created for the child.
Projections are also treated differently in the VM for efficiency.

Note that projections have nothing to do with the dot `mylist.map` syntax.

You can find out if a declaration is a projection using `environment.is_projection` which returns `projection_info`.

Data for a projection declaration:
- `cname`    is the name of the constructor associated with the projection.
- `nparams`  is the number of constructor parameters. Eg `and.intro` has two type parameters.
- `idx`      is the parameter being projected by this projection.
- `is_class` is tt iff this is a typeclass projection.

### Examples:

- `and.right` is a projection with ``{cname := `and.intro, nparams := 2, idx := 1, is_class := ff}``
- `ordered_ring.neg` is a projection with ``{cname := `ordered_ring.mk, nparams := 1, idx := 5, is_class := tt}``.

-/
structure ProjectionInfo where
  cname : Name
  nparams : Nat
  idx : Nat
  isClass : Bool

/-- A marking on the binders of structures and inductives indicating
   how this constructor should mark its parameters.

       inductive foo
       | one {} : foo -> foo   -- relaxed_implicit
       | two ( ) : foo -> foo  -- explicit
       | two [] : foo -> foo   -- implicit
       | three : foo -> foo    -- relaxed implicit (default)
-/
inductive ImplicitInferKind
  | implicit
  | relaxed_implicit
  | none

instance ImplicitInferKind.inhabited : Inhabited ImplicitInferKind :=
  ⟨ImplicitInferKind.implicit⟩

/-- One introduction rule in an inductive declaration -/
unsafe structure intro_rule where
  constr : Name
  type : expr
  infer : ImplicitInferKind := ImplicitInferKind.implicit

/-- Create a standard environment using the given trust level -/
unsafe axiom mk_std : Nat → environment

/-- Return the trust level of the given environment -/
unsafe axiom trust_lvl : environment → Nat

/-- Add a new declaration to the environment -/
unsafe axiom add : environment → declaration → exceptional environment

/-- make declaration `n` protected -/
unsafe axiom mk_protected : environment → Name → environment

/-- add declaration `d` and make it protected -/
unsafe def add_protected (env : environment) (d : declaration) : exceptional environment := do
  let env ← env.add d
  pure <| env d

/-- check if `n` is the name of a protected declaration -/
unsafe axiom is_protected : environment → Name → Bool

/-- Retrieve a declaration from the environment -/
unsafe axiom get : environment → Name → exceptional declaration

unsafe def contains (env : environment) (d : Name) : Bool :=
  match env.get d with
  | exceptional.success _ => true
  | exceptional.exception _ => false

unsafe axiom add_defn_eqns (env : environment) (opt : options) (lp_params : List Name) (params : List expr) (sig : expr)
    (eqns : List (List (expr false) × expr)) (is_meta : Bool) : exceptional environment

/-- Register the given name as a namespace, making it available to the `open` command -/
unsafe axiom add_namespace : environment → Name → environment

/-- Mark a namespace as open -/
unsafe axiom mark_namespace_as_open : environment → Name → environment

/-- Modify the environment as if `open %%name` had been parsed -/
unsafe axiom execute_open : environment → Name → environment

/-- Retrieve all registered namespaces -/
unsafe axiom get_namespaces : environment → List Name

/-- Return tt iff the given name is a namespace -/
unsafe axiom is_namespace : environment → Name → Bool

/-- Add a new inductive datatype to the environment
   name, universe parameters, number of parameters, type, constructors (name and type), is_meta -/
unsafe axiom add_inductive (env : environment) (n : Name) (levels : List Name) (num_params : Nat) (type : expr)
    (intros : List (Name × expr)) (is_meta : Bool) : exceptional environment

/-- Add a new general inductive declaration to the environment.
  This has the same effect as a `inductive` in the file, including generating
  all the auxiliary definitions, as well as triggering mutual/nested inductive
  compilation, by contrast to `environment.add_inductive` which only adds the
  core axioms supported by the kernel.

  The `inds` argument should be a list of inductives in the mutual family.
  The first argument is a pair of the name of the type being constructed
  and the type of this inductive family (not including the params).
  The second argument is a list of intro rules, specified by a name, an
  `implicit_infer_kind` giving the implicitness of the params for this constructor,
  and an expression with the type of the constructor (not including the params).
-/
unsafe axiom add_ginductive (env : environment) (opt : options) (levels : List Name) (params : List expr)
    (inds : List ((Name × expr) × List intro_rule)) (is_meta : Bool) : exceptional environment

/-- Return tt iff the given name is an inductive datatype -/
unsafe axiom is_inductive : environment → Name → Bool

/-- Return tt iff the given name is a constructor -/
unsafe axiom is_constructor : environment → Name → Bool

/-- Return tt iff the given name is a recursor -/
unsafe axiom is_recursor : environment → Name → Bool

/-- Return tt iff the given name is a recursive inductive datatype -/
unsafe axiom is_recursive : environment → Name → Bool

/-- Return the name of the inductive datatype of the given constructor. -/
unsafe axiom inductive_type_of : environment → Name → Option Name

/-- Return the constructors of the inductive datatype with the given name -/
unsafe axiom constructors_of : environment → Name → List Name

/-- Return the recursor of the given inductive datatype -/
unsafe axiom recursor_of : environment → Name → Option Name

/-- Return the number of parameters of the inductive datatype -/
unsafe axiom inductive_num_params : environment → Name → Nat

/-- Return the number of indices of the inductive datatype -/
unsafe axiom inductive_num_indices : environment → Name → Nat

/-- Return tt iff the inductive datatype recursor supports dependent elimination -/
unsafe axiom inductive_dep_elim : environment → Name → Bool

/-- Functionally equivalent to `is_inductive`.

Technically, this works by checking if the name is in the ginductive environment
extension which is outside the kernel, whereas `is_inductive` works by looking at the kernel extension.
But there are no `is_inductive`s which are not `is_ginductive`.
 -/
unsafe axiom is_ginductive : environment → Name → Bool

/-- See the docstring for `projection_info`. -/
unsafe axiom is_projection : environment → Name → Option ProjectionInfo

/-- Fold over declarations in the environment. -/
unsafe axiom fold {α : Type} : environment → α → (declaration → α → α) → α

/-- `relation_info env n` returns some value if n is marked as a relation in the given environment.
   the tuple contains: total number of arguments of the relation, lhs position and rhs position. -/
unsafe axiom relation_info : environment → Name → Option (Nat × Nat × Nat)

/-- `refl_for env R` returns the name of the reflexivity theorem for the relation R -/
unsafe axiom refl_for : environment → Name → Option Name

/-- `symm_for env R` returns the name of the symmetry theorem for the relation R -/
unsafe axiom symm_for : environment → Name → Option Name

/-- `trans_for env R` returns the name of the transitivity theorem for the relation R -/
unsafe axiom trans_for : environment → Name → Option Name

/-- `decl_olean env d` returns the name of the .olean file where d was defined.
   The result is none if d was not defined in an imported file. -/
unsafe axiom decl_olean : environment → Name → Option Stringₓ

/-- `decl_pos env d` returns the source location of d if available. -/
unsafe axiom decl_pos : environment → Name → Option Pos

/-- `decl_pos env d` returns the name of a declaration that d inherits
noncomputability from, or `none` if it is computable.

Note that this also returns `none` on `axiom`s and `constant`s. These can be detected by using
`environment.get_decl` and `declaration.is_axiom` and `declaration.is_constant`. -/
unsafe axiom decl_noncomputable_reason : environment → Name → Option Name

/-- Return the fields of the structure with the given name, or `none` if it is not a structure -/
unsafe axiom structure_fields : environment → Name → Option (List Name)

/-- `get_class_attribute_symbols env attr_name` return symbols
   occurring in instances of type classes tagged with the attribute `attr_name`.
   Example: [algebra] -/
unsafe axiom get_class_attribute_symbols : environment → Name → name_set

/-- The fingerprint of the environment is a hash formed from all of the declarations in the environment. -/
unsafe axiom fingerprint : environment → Nat

/-- Gets the equation lemmas for the declaration `n`. -/
unsafe axiom get_eqn_lemmas_for (env : environment) (n : Name) : List Name

/-- Gets the equation lemmas for the declaration `n`, including lemmas for match statements, etc. -/
unsafe axiom get_ext_eqn_lemmas_for (env : environment) (n : Name) : List Name

/-- Adds the equation lemma `n`.
It is added for the declaration `t.pi_codomain.get_app_fn.const_name` where `t` is the type of the equation lemma.
-/
unsafe axiom add_eqn_lemma (env : environment) (n : Name) : environment

open Expr

unsafe axiom unfold_untrusted_macros : environment → expr → expr

unsafe axiom unfold_all_macros : environment → expr → expr

unsafe def is_constructor_app (env : environment) (e : expr) : Bool :=
  is_constant (get_app_fn e) && is_constructor env (const_name (get_app_fn e))

unsafe def is_refl_app (env : environment) (e : expr) : Option (Name × expr × expr) :=
  match refl_for env (const_name (get_app_fn e)) with
  | some n => if get_app_num_args e ≥ 2 then some (n, app_arg (app_fn e), app_arg e) else none
  | none => none

/-- Return true if 'n' has been declared in the current file -/
unsafe def in_current_file (env : environment) (n : Name) : Bool :=
  (env.decl_olean n).isNone && env.contains n && n ∉ [`` Quot, `` Quot.mk, `` Quot.lift, `` Quot.ind]

unsafe def is_definition (env : environment) (n : Name) : Bool :=
  match env.get n with
  | exceptional.success (declaration.defn _ _ _ _ _ _) => true
  | _ => false

end Environment

unsafe instance : HasRepr environment :=
  ⟨fun e => "[environment]"⟩

unsafe instance : Inhabited environment :=
  ⟨environment.mk_std 0⟩

