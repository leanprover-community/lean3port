/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.coe
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.List.Basic
import Leanbin.Init.Data.Subtype.Basic
import Leanbin.Init.Data.Prod

/-! # Coercions and lifts

The elaborator tries to insert coercions automatically.
Only instances of `has_coe` type class are considered in the process.

Lean also provides a "lifting" operator: `↑a`.
It uses all instances of `has_lift` type class.
Every `has_coe` instance is also a `has_lift` instance.

We recommend users only use `has_coe` for coercions that do not produce a lot
of ambiguity.

All coercions and lifts can be identified with the constant `coe`.

We use the `has_coe_to_fun` type class for encoding coercions from
a type to a function space.

We use the `has_coe_to_sort` type class for encoding coercions from
a type to a sort.
-/


universe u v

/-- Can perform a lifting operation `↑a`. -/
class HasLift (a : Sort u) (b : Sort v) where
  lift : a → b
#align has_lift HasLift

/-- Auxiliary class that contains the transitive closure of `has_lift`. -/
class HasLiftT (a : Sort u) (b : Sort v) where
  lift : a → b
#align has_lift_t HasLiftT

/-!
We specify the universes in `has_coe`, `has_coe_to_fun`, and `has_coe_to_sort`
explicitly in order to match exactly what appears in Lean4.
-/


#print Coe /-
class Coe (a : Sort u) (b : Sort v) : Sort max max 1 u v where
  coe : a → b
#align has_coe Coe
-/

/-- Auxiliary class that contains the transitive closure of `has_coe`. -/
class CoeTC (a : Sort u) (b : Sort v) where
  coe : a → b
#align has_coe_t CoeTCₓ

#print CoeFun /-
class CoeFun (a : Sort u) (F : outParam (a → Sort v)) : Sort max max 1 u v where
  coe : ∀ x, F x
#align has_coe_to_fun CoeFun
-/

#print CoeSort /-
class CoeSort (a : Sort u) (S : outParam (Sort v)) : Sort max max 1 u v where
  coe : a → S
#align has_coe_to_sort CoeSort
-/

def lift {a : Sort u} {b : Sort v} [HasLift a b] : a → b :=
  @HasLift.lift a b _
#align lift lift

def liftT {a : Sort u} {b : Sort v} [HasLiftT a b] : a → b :=
  @HasLiftT.lift a b _
#align lift_t liftT

def coeB {a : Sort u} {b : Sort v} [Coe a b] : a → b :=
  @Coe.coe a b _
#align coe_b coeB

def coeT {a : Sort u} {b : Sort v} [CoeTC a b] : a → b :=
  @CoeTC.coe a b _
#align coe_t coeT

def coeFnB {a : Sort u} {b : a → Sort v} [CoeFun a b] : ∀ x : a, b x :=
  CoeFun.coe
#align coe_fn_b coeFnB

/-! ### User level coercion operators -/


@[reducible]
def coe {a : Sort u} {b : Sort v} [HasLiftT a b] : a → b :=
  liftT
#align coe coe

@[reducible]
def coeFn {a : Sort u} {b : a → Sort v} [CoeFun a b] : ∀ x : a, b x :=
  CoeFun.coe
#align coe_fn coeFn

@[reducible]
def coeSort {a : Sort u} {b : Sort v} [CoeSort a b] : a → b :=
  CoeSort.coe
#align coe_sort coeSort

/-! ### Notation -/


-- mathport name: «expr⇑ »
notation:arg "⇑" x:arg => coeFn x

-- mathport name: «expr↥ »
notation:arg "↥" x:arg => coeSort x

universe u₁ u₂ u₃

/-! ### Transitive closure for `has_lift`, `has_coe`, `has_coe_to_fun` -/


instance liftTrans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [HasLiftT b c] [HasLift a b] :
    HasLiftT a c :=
  ⟨fun x => liftT (lift x : b)⟩
#align lift_trans liftTrans

instance liftBase {a : Sort u} {b : Sort v} [HasLift a b] : HasLiftT a b :=
  ⟨lift⟩
#align lift_base liftBase

instance coeTrans {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [CoeTC b c] [Coe a b] : CoeTC a c :=
  ⟨fun x => coeT (coeB x : b)⟩
#align coe_trans coeTransₓ

instance coeBase {a : Sort u} {b : Sort v} [Coe a b] : CoeTC a b :=
  ⟨coeB⟩
#align coe_base coeBaseₓ

/-- We add this instance directly into `has_coe_t` to avoid non-termination.

   Suppose coe_option had type `(has_coe a (option a))`.
   Then, we can loop when searching a coercion from `α` to `β` `(has_coe_t α β)`
   1. `coe_trans at (has_coe_t α β)`
          `(has_coe α ?b₁) and (has_coe_t ?b₁ c)`
   2. `coe_option at (has_coe α ?b₁)`
          `?b₁ := option α`
   3. `coe_trans at (has_coe_t (option α) β)`
          `(has_coe (option α) ?b₂) and (has_coe_t ?b₂ β)`
   4. `coe_option at (has_coe (option α) ?b₂)`
          `?b₂ := option (option α))`
   ... -/
instance coeOption {a : Type u} : CoeTC a (Option a) :=
  ⟨fun x => some x⟩
#align coe_option coeOption

/-- Auxiliary transitive closure for `has_coe` which does not contain
   instances such as `coe_option`.

   They would produce non-termination when combined with `coe_fn_trans` and `coe_sort_trans`. -/
class HasCoeTAux (a : Sort u) (b : Sort v) where
  coe : a → b
#align has_coe_t_aux HasCoeTAux

instance coeTransAux {a : Sort u₁} {b : Sort u₂} {c : Sort u₃} [HasCoeTAux b c] [Coe a b] :
    HasCoeTAux a c :=
  ⟨fun x : a => @HasCoeTAux.coe b c _ (coeB x)⟩
#align coe_trans_aux coeTransAux

instance coeBaseAux {a : Sort u} {b : Sort v} [Coe a b] : HasCoeTAux a b :=
  ⟨coeB⟩
#align coe_base_aux coeBaseAux

instance coeFnTrans {a : Sort u₁} {b : Sort u₂} {c : b → Sort v} [CoeFun b c] [HasCoeTAux a b] :
    CoeFun a fun x => c (@HasCoeTAux.coe a b _ x) :=
  ⟨fun x => coeFn (@HasCoeTAux.coe a b _ x)⟩
#align coe_fn_trans coeFnTrans

instance coeSortTrans {a : Sort u₁} {b : Sort u₂} {c : Sort v} [CoeSort b c] [HasCoeTAux a b] :
    CoeSort a c :=
  ⟨fun x => coeSort (@HasCoeTAux.coe a b _ x)⟩
#align coe_sort_trans coeSortTrans

/-- Every coercion is also a lift -/
instance coeToLift {a : Sort u} {b : Sort v} [CoeTC a b] : HasLiftT a b :=
  ⟨coeT⟩
#align coe_to_lift coeToLift

/-! ### Basic coercions -/


instance coeBoolToProp : Coe Bool Prop :=
  ⟨fun y => y = tt⟩
#align coe_bool_to_Prop coeBoolToProp

/--
Tactics such as the simplifier only unfold reducible constants when checking whether two terms are definitionally
   equal or a term is a proposition. The motivation is performance.
   In particular, when simplifying `p -> q`, the tactic `simp` only visits `p` if it can establish that it is a proposition.
   Thus, we mark the following instance as `@[reducible]`, otherwise `simp` will not visit `↑p` when simplifying `↑p -> q`.
-/
@[reducible]
instance coeSortBool : CoeSort Bool Prop :=
  ⟨fun y => y = tt⟩
#align coe_sort_bool coeSortBool

instance coeDecidableEq (x : Bool) : Decidable (coe x) :=
  show Decidable (x = tt) from Bool.decidableEq x true
#align coe_decidable_eq coeDecidableEq

instance coeSubtype {a : Sort u} {p : a → Prop} : Coe { x // p x } a :=
  ⟨Subtype.val⟩
#align coe_subtype coeSubtype

/-! ### Basic lifts -/


universe ua ua₁ ua₂ ub ub₁ ub₂

/--
Remark: we can't use `[has_lift_t a₂ a₁]` since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/
instance liftFn {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [HasLift a₂ a₁]
    [HasLiftT b₁ b₂] : HasLift (a₁ → b₁) (a₂ → b₂) :=
  ⟨fun f x => ↑(f ↑x)⟩
#align lift_fn liftFn

instance liftFnRange {a : Sort ua} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [HasLiftT b₁ b₂] :
    HasLift (a → b₁) (a → b₂) :=
  ⟨fun f x => ↑(f x)⟩
#align lift_fn_range liftFnRange

/-- A dependent version of `lift_fn_range`. -/
instance liftPiRange {α : Sort u} {A : α → Sort ua} {B : α → Sort ub} [∀ i, HasLiftT (A i) (B i)] :
    HasLift (∀ i, A i) (∀ i, B i) :=
  ⟨fun f i => ↑(f i)⟩
#align lift_pi_range liftPiRange

instance liftFnDom {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b : Sort ub} [HasLift a₂ a₁] :
    HasLift (a₁ → b) (a₂ → b) :=
  ⟨fun f x => f ↑x⟩
#align lift_fn_dom liftFnDom

instance liftPair {a₁ : Type ua₁} {a₂ : Type ub₂} {b₁ : Type ub₁} {b₂ : Type ub₂} [HasLiftT a₁ a₂]
    [HasLiftT b₁ b₂] : HasLift (a₁ × b₁) (a₂ × b₂) :=
  ⟨fun p => Prod.casesOn p fun x y => (↑x, ↑y)⟩
#align lift_pair liftPair

instance liftPair₁ {a₁ : Type ua₁} {a₂ : Type ua₂} {b : Type ub} [HasLiftT a₁ a₂] :
    HasLift (a₁ × b) (a₂ × b) :=
  ⟨fun p => Prod.casesOn p fun x y => (↑x, y)⟩
#align lift_pair₁ liftPair₁

instance liftPair₂ {a : Type ua} {b₁ : Type ub₁} {b₂ : Type ub₂} [HasLiftT b₁ b₂] :
    HasLift (a × b₁) (a × b₂) :=
  ⟨fun p => Prod.casesOn p fun x y => (x, ↑y)⟩
#align lift_pair₂ liftPair₂

instance liftList {a : Type u} {b : Type v} [HasLift a b] : HasLift (List a) (List b) :=
  ⟨fun l => List.map coe l⟩
#align lift_list liftList

