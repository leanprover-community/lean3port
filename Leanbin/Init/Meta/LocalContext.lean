prelude
import Leanbin.Init.Meta.Name
import Leanbin.Init.Meta.Expr
import Leanbin.Init.Data.Option.Basic

unsafe structure local_decl where
  unique_name : Name
  pp_name : Name
  type : expr
  value : Option expr
  bi : BinderInfo
  idx : Nat

unsafe def local_decl.to_expr : local_decl → expr
  | ⟨un, pn, y, _, bi, _⟩ => expr.local_const un pn bi y

/-- A local context is a list of local constant declarations.
Each metavariable in a metavariable context holds a local_context
to declare which locals the metavariable is allowed to depend on. -/
unsafe axiom local_context : Type

namespace LocalContext

/-- The empty local context. -/
unsafe axiom empty : local_context

/-- Add a new local constant to the lc. The new local has an unused unique_name.
Fails when the type depends on local constants that are not present in the context.-/
unsafe axiom mk_local (pretty_name : Name) (type : expr) (bi : BinderInfo) :
    local_context → Option (expr × local_context)

unsafe axiom get_local_decl : Name → local_context → Option local_decl

unsafe axiom get_local : Name → local_context → Option expr

unsafe axiom is_subset : local_context → local_context → Bool

unsafe axiom has_decidable_eq : DecidableEq local_context

attribute [instance] has_decidable_eq

unsafe axiom fold {α : Type} (f : α → expr → α) : α → local_context → α

unsafe def to_list : local_context → List expr :=
  List.reverse ∘ fold (fun acc e => e :: Acc) []

unsafe def to_format : local_context → format :=
  to_fmt ∘ to_list

unsafe instance : has_to_format local_context :=
  ⟨to_format⟩

unsafe instance : LE local_context :=
  ⟨fun a b => local_context.is_subset a b⟩

unsafe instance decidable_rel : DecidableRel ((· ≤ ·) : local_context → local_context → Prop) :=
  inferInstance

unsafe instance : HasEmptyc local_context :=
  ⟨empty⟩

unsafe instance : Inhabited local_context :=
  ⟨empty⟩

unsafe instance : HasMem expr local_context :=
  ⟨fun e lc => Option.isSome <| get_local (expr.local_uniq_name e) lc⟩

unsafe instance {e : expr} {lc : local_context} : Decidable (e ∈ lc) :=
  inferInstance

end LocalContext

