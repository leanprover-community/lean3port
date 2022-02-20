/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Leanbin.Init.Meta.Environment
import Leanbin.Init.Meta.Tactic

/-- Information about a currently loaded module (such as `data.dlist`). -/
unsafe axiom module_info : Type

namespace ModuleInfo

/-- The absolute path to the `.lean` file containing the module (e.g. `".../data/dlist.lean"`). -/
@[reducible]
unsafe def module_id :=
  Stringₓ

/-- The name of the module, as used in an import command (e.g. `data.dlist`). -/
@[reducible]
unsafe def module_name :=
  Name

/-- Resolves a `module_name` to `module_id`, using the global search path.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**
-/
unsafe axiom resolve_module_name (name : module_name) (cur_module : module_id := "") : module_id

/-- Retrieves the module with the given `module_id`.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**

This function is constant-time if the module is already a dependency.
-/
unsafe axiom of_module_id (id : module_id) : module_info

/-- Retrieves the module with the given `module_name`.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**

This function is constant-time if the module is already a dependency.
-/
unsafe def of_module_name (name : module_name) (cur_module : module_id := "") : module_info :=
  of_module_id (resolve_module_name Name cur_module)

/-- Returns the `module_id` of the module. -/
protected unsafe axiom id : module_info → module_id

unsafe instance : HasRepr module_info :=
  ⟨module_info.id⟩

unsafe instance : HasToString module_info :=
  ⟨module_info.id⟩

unsafe instance : has_to_format module_info :=
  ⟨fun m => to_fmt m.id⟩

unsafe instance : has_to_tactic_format module_info :=
  ⟨tactic.pp ∘ module_info.id⟩

end ModuleInfo

open ModuleInfo

namespace Environment

/-- Imports the dependencies of a module into an environment.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**

Already imported dependencies will not be imported twice.
-/
unsafe axiom import_dependencies : environment → module_info → environment

/-- Imports only the module (without the dependencies) into an environment.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**
-/
unsafe axiom import_only : environment → module_info → environment

/-- Imports all declarations until `decl_name` of the module (without the dependencies) into an environment.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**
-/
unsafe axiom import_only_until_decl (env : environment) (mod_info : module_info) (decl_name : Name) : environment

/-- Imports a module including dependencies into an environment.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**
-/
unsafe def import' (env : environment) (mi : module_info) : environment :=
  (env.import_dependencies mi).import_only mi

/-- Imports a module until `decl_name` including dependencies into an environment.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**
-/
unsafe def import_until_decl (env : environment) (mi : module_info) (decl_name : Name) : environment :=
  (env.import_dependencies mi).import_only_until_decl mi decl_name

/-- Creates an environment containing the module `id` including dependencies.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**

The environment `from_imported_module ".../data/dlist.lean"` is roughly equivalent to
the environment at the end of a file containing just `import data.dlist`.
-/
unsafe def from_imported_module (id : module_id) : environment :=
  (mk_std 1025).import' (of_module_id id)

/-- Creates an environment containing the module `id` until `decl_name` including dependencies.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**
-/
unsafe def for_decl_of_imported_module (id : module_id) (decl_name : Name) : environment :=
  (mk_std 1025).import_until_decl (of_module_id id) decl_name

/-- Creates an environment containing the module `name` including dependencies.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**
-/
unsafe def from_imported_module_name (name : module_name) (cur_module := "") : environment :=
  from_imported_module (resolve_module_name Name cur_module)

/-- Creates an environment containing the module `name` until declaration `decl_name`
including dependencies.

**ONLY USE THIS FUNCTION IN (CI) SCRIPTS!**
-/
unsafe def for_decl_of_imported_module_name (mod_nam : module_name) (decl : Name) (cur_mod := "") : environment :=
  for_decl_of_imported_module (resolve_module_name mod_nam cur_mod) decl

end Environment

