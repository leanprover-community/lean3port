/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.Meta.Tactic
import Init.Meta.RbMap
import Init.Meta.HasReflect
import Init.Meta.Lean.Parser

#align_import init.meta.attribute from "leanprover-community/lean"@"e77a64739870401e78ef3294bb95b8733b900cba"

/-- Get all of the declaration names that have the given attribute.
Eg. ``get_instances `simp`` returns a list with the names of all of the lemmas in the environment tagged with the `@[simp]` attribute.
 -/
unsafe axiom attribute.get_instances : Name → tactic (List Name)
#align attribute.get_instances attribute.get_instances

/--
Returns a hash of `get_instances`. You can use this to tell if your attribute instances have changed. -/
unsafe axiom attribute.fingerprint : Name → tactic Nat
#align attribute.fingerprint attribute.fingerprint

/--
Configuration for a user attribute cache. For example, the `simp` attribute has a cache of type simp_lemmas.
- `mk_cache` is a function where you are given all of the declarations tagged with your attribute and you return the new value for the cache.
  That is, `mk_cache` makes the object you want to be cached.
- `dependencies` is a list of other attributes whose caches need to be computed first.
-/
unsafe structure user_attribute_cache_cfg (cache_ty : Type) where
  mk_cache : List Name → tactic cache_ty
  dependencies : List Name
#align user_attribute_cache_cfg user_attribute_cache_cfg

/-- Close the current goal by filling it with the trivial `user_attribute_cache_cfg unit`. -/
unsafe def user_attribute.dflt_cache_cfg : tactic Unit :=
  tactic.exact q((⟨fun _ => pure (), []⟩ : user_attribute_cache_cfg Unit))
#align user_attribute.dflt_cache_cfg user_attribute.dflt_cache_cfg

unsafe def user_attribute.dflt_parser : tactic Unit :=
  tactic.exact q((pure () : lean.parser Unit))
#align user_attribute.dflt_parser user_attribute.dflt_parser

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic user_attribute.dflt_cache_cfg -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic user_attribute.dflt_parser -/
/-- A __user attribute__ is an attribute defined by the user (ie, not built in to Lean).
### Type parameters
- `cache_ty` is the type of a cached VM object that is computed from all of the declarations in the environment tagged with this attribute.
- `param_ty` is an argument for the attribute when it is used. For instance with `param_ty` being `ℕ` you could write `@[my_attribute 4]`.

### Data
A `user_attribute` consists of the following pieces of data:
- `name` is the name of the attribute, eg ```simp```
- `descr` is a plaintext description of the attribute for humans.
- `after_set` is an optional handler that will be called after the attribute has been applied to a declaration.
    Failing the tactic will fail the entire `attribute/def/...` command, i.e. the attribute will
    not be applied after all.
    Declaring an `after_set` handler without a `before_unset` handler will make the attribute
    non-removable.
- `before_unset` Optional handler that will be called before the attribute is removed from a declaration.
- `cache_cfg` describes how to construct the user attribute's cache. See docstring for `user_attribute_cache_cfg`
- `reflect_param` demands that `param_ty` can be reflected.
    This means we have a function from `param_ty` to an expr.
    See the docstring for `has_reflect`.
- `parser` Parser that will be invoked after parsing the attribute's name. The parse result will be reflected
and stored and can be retrieved with `user_attribute.get_param`.
 -/
unsafe structure user_attribute (cache_ty : Type := Unit) (param_ty : Type := Unit) where
  Name : Name
  descr : String
  after_set : Option (∀ (decl : Name) (prio : Nat) (persistent : Bool), Tactic) := none
  before_unset : Option (∀ (decl : Name) (persistent : Bool), Tactic) := none
  cache_cfg : user_attribute_cache_cfg cache_ty := by
    run_tac
      user_attribute.dflt_cache_cfg
  [reflect_param : has_reflect param_ty]
  parser : lean.parser param_ty := by
    run_tac
      user_attribute.dflt_parser
#align user_attribute user_attribute

/-- Registers a new user-defined attribute. The argument must be the name of a definition of type
   `user_attribute α β`. Once registered, you may tag declarations with this attribute. -/
unsafe def attribute.register (decl : Name) : Tactic :=
  tactic.set_basic_attribute `` user_attribute decl true
#align attribute.register attribute.register

/-- Returns the attribute cache for the given user attribute. -/
unsafe axiom user_attribute.get_cache {α β : Type} (attr : user_attribute α β) : tactic α
#align user_attribute.get_cache user_attribute.get_cache

unsafe def user_attribute.parse_reflect {α β : Type} (attr : user_attribute α β) :
    lean.parser expr :=
  (fun a => attr.reflect_param a) <$> attr.parser
#align user_attribute.parse_reflect user_attribute.parse_reflect

unsafe axiom user_attribute.get_param_untyped {α β : Type} (attr : user_attribute α β)
    (decl : Name) : tactic expr
#align user_attribute.get_param_untyped user_attribute.get_param_untyped

unsafe axiom user_attribute.set_untyped {α β : Type} [reflected _ β] (attr : user_attribute α β)
    (decl : Name) (val : expr) (persistent : Bool) (prio : Option Nat := none) : tactic Unit
#align user_attribute.set_untyped user_attribute.set_untyped

/--
Get the value of the parameter for the attribute on a given declatation. Will fail if the attribute does not exist.-/
unsafe def user_attribute.get_param {α β : Type} [reflected _ β] (attr : user_attribute α β)
    (n : Name) : tactic β :=
  attr.get_param_untyped n >>= tactic.eval_expr β
#align user_attribute.get_param user_attribute.get_param

unsafe def user_attribute.set {α β : Type} [reflected _ β] (attr : user_attribute α β) (n : Name)
    (val : β) (persistent : Bool) (prio : Option Nat := none) : tactic Unit :=
  attr.set_untyped n (attr.reflect_param val) persistent prio
#align user_attribute.set user_attribute.set

open Tactic

/-- Alias for attribute.register -/
unsafe def register_attribute :=
  attribute.register
#align register_attribute register_attribute

unsafe def get_attribute_cache_dyn {α : Type} [reflected _ α] (attr_decl_name : Name) : tactic α :=
  let attr : pexpr := expr.const attr_decl_name []
  do
  let e ← to_expr ``(user_attribute.get_cache $(attr))
  let t ← eval_expr (tactic α) e
  t
#align get_attribute_cache_dyn get_attribute_cache_dyn

unsafe def mk_name_set_attr (attr_name : Name) : Tactic := do
  let t := q(user_attribute name_set)
  let v :=
    q(({  Name := attr_name
          descr := "name_set attribute"
          cache_cfg :=
            { mk_cache := fun ns => return (name_set.of_list ns)
              dependencies := [] } } :
        user_attribute name_set))
  add_meta_definition attr_name [] t v
  register_attribute attr_name
#align mk_name_set_attr mk_name_set_attr

unsafe def get_name_set_for_attr (name : Name) : tactic name_set :=
  get_attribute_cache_dyn Name
#align get_name_set_for_attr get_name_set_for_attr

