/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Leanbin.Init.Meta.Expr
import Leanbin.Init.Meta.Name
import Leanbin.Init.Meta.Task

/-- Reducibility hints are used in the convertibility checker.
When trying to solve a constraint such a

           (f ...) =?= (g ...)

where f and g are definitions, the checker has to decide which one will be unfolded.
  If      f (g) is opaque,     then g (f) is unfolded if it is also not marked as opaque,
  Else if f (g) is abbrev,     then f (g) is unfolded if g (f) is also not marked as abbrev,
  Else if f and g are regular, then we unfold the one with the biggest definitional height.
  Otherwise both are unfolded.

The arguments of the `regular` constructor are: the definitional height and the flag `self_opt`.

The definitional height is by default computed by the kernel. It only takes into account
other regular definitions used in a definition. When creating declarations using meta-programming,
we can specify the definitional depth manually.

For definitions marked as regular, we also have a hint for constraints such as

          (f a) =?= (f b)

if self_opt == true, then checker will first try to solve (a =?= b), only if it fails,
it unfolds f.

Remark: the hint only affects performance. None of the hints prevent the kernel from unfolding a
declaration during type checking.

Remark: the reducibility_hints are not related to the attributes: reducible/irrelevance/semireducible.
These attributes are used by the elaborator. The reducibility_hints are used by the kernel (and elaborator).
Moreover, the reducibility_hints cannot be changed after a declaration is added to the kernel.
-/
inductive ReducibilityHints
  | opaque : ReducibilityHints
  | abbrev : ReducibilityHints
  | regular : Nat → Bool → ReducibilityHints

/-- Reflect a C++ declaration object. The VM replaces it with the C++ implementation. -/
unsafe inductive declaration-- definition: name, list universe parameters, type, value, is_trusted

  | defn :
    Name →
      List Name →
        expr →
          expr →
            ReducibilityHints →
              Bool →
                declaration-- theorem: name, list universe parameters, type, value (remark: theorems are always trusted)

  | thm :
    Name →
      List Name → expr → task expr → declaration-- constant assumption: name, list universe parameters, type, is_trusted

  | cnst :
    Name →
      List Name →
        expr → Bool → declaration-- axiom : name → list universe parameters, type (remark: axioms are always trusted)

  | ax : Name → List Name → expr → declaration

open Declaration

unsafe def mk_definition (n : Name) (ls : List Name) (v : expr) (e : expr) : declaration :=
  defn n ls v e (ReducibilityHints.regular 1 true) true

namespace Declaration

unsafe def to_name : declaration → Name
  | defn n _ _ _ _ _ => n
  | thm n _ _ _ => n
  | cnst n _ _ _ => n
  | ax n _ _ => n

unsafe def univ_params : declaration → List Name
  | defn _ ls _ _ _ _ => ls
  | thm _ ls _ _ => ls
  | cnst _ ls _ _ => ls
  | ax _ ls _ => ls

unsafe def type : declaration → expr
  | defn _ _ t _ _ _ => t
  | thm _ _ t _ => t
  | cnst _ _ t _ => t
  | ax _ _ t => t

unsafe def value : declaration → expr
  | defn _ _ _ v _ _ => v
  | thm _ _ _ v => v.get
  | _ => default

unsafe def value_task : declaration → task expr
  | defn _ _ _ v _ _ => task.pure v
  | thm _ _ _ v => v
  | _ => task.pure default

unsafe def is_trusted : declaration → Bool
  | defn _ _ _ _ _ t => t
  | cnst _ _ _ t => t
  | _ => true

unsafe def update_type : declaration → expr → declaration
  | defn n ls t v h tr, new_t => defn n ls new_t v h tr
  | thm n ls t v, new_t => thm n ls new_t v
  | cnst n ls t tr, new_t => cnst n ls new_t tr
  | ax n ls t, new_t => ax n ls new_t

unsafe def update_name : declaration → Name → declaration
  | defn n ls t v h tr, new_n => defn new_n ls t v h tr
  | thm n ls t v, new_n => thm new_n ls t v
  | cnst n ls t tr, new_n => cnst new_n ls t tr
  | ax n ls t, new_n => ax new_n ls t

unsafe def update_value : declaration → expr → declaration
  | defn n ls t v h tr, new_v => defn n ls t new_v h tr
  | thm n ls t v, new_v => thm n ls t (task.pure new_v)
  | d, new_v => d

unsafe def update_value_task : declaration → task expr → declaration
  | defn n ls t v h tr, new_v => defn n ls t new_v.get h tr
  | thm n ls t v, new_v => thm n ls t new_v
  | d, new_v => d

unsafe def map_value : declaration → (expr → expr) → declaration
  | defn n ls t v h tr, f => defn n ls t (f v) h tr
  | thm n ls t v, f => thm n ls t (task.map f v)
  | d, f => d

unsafe def to_definition : declaration → declaration
  | cnst n ls t tr => defn n ls t default ReducibilityHints.abbrev tr
  | ax n ls t => thm n ls t (task.pure default)
  | d => d

unsafe def is_definition : declaration → Bool
  | defn _ _ _ _ _ _ => true
  | _ => false

/-- Instantiate a universe polymorphic declaration type with the given universes. -/
unsafe axiom instantiate_type_univ_params : declaration → List level → Option expr

/-- Instantiate a universe polymorphic declaration value with the given universes. -/
unsafe axiom instantiate_value_univ_params : declaration → List level → Option expr

end Declaration

