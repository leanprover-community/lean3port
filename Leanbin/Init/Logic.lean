/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
import Leanbin.Init.Core

universe u v w

-- implication
def Implies (a b : Prop) :=
  a → b

/-- Implication `→` is transitive. If `P → Q` and `Q → R` then `P → R`. -/
@[trans]
theorem Implies.trans {p q r : Prop} (h₁ : Implies p q) (h₂ : Implies q r) : Implies p r := fun hp => h₂ (h₁ hp)

def NonContradictory (a : Prop) : Prop :=
  ¬¬a

section

variable {α β φ : Sort u} {a a' : α} {b b' : β} {c : φ}

end

theorem eq_rec_compose :
    ∀ {α β φ : Sort u} (p₁ : β = φ) (p₂ : α = β) (a : α),
      (Eq.recOn p₁ (Eq.recOn p₂ a : β) : φ) = Eq.recOn (Eq.trans p₂ p₁) a
  | α, _, _, rfl, rfl, a => rfl

-- and
variable {a b c d : Prop}

theorem And.swap : a ∧ b → b ∧ a := fun ⟨ha, hb⟩ => ⟨hb, ha⟩

-- xor
@[simp] abbrev Xorₓ (a b : Prop) := xor a b

-- decidable
def Decidable.toBool (p : Prop) [h : Decidable p] : Bool :=
  Decidable.casesOn h (fun h₁ => Bool.false) fun h₂ => Bool.true

export Decidable (isTrue isFalse toBool)

@[simp]
theorem to_bool_true_eq_tt (h : Decidable True) : @toBool True h = true :=
  Decidable.casesOn h (fun h => False.elim (Iff.mp not_true h)) fun _ => rfl

@[simp]
theorem to_bool_false_eq_ff (h : Decidable False) : @toBool False h = false :=
  Decidable.casesOn h (fun h => rfl) fun h => False.elim h

section

variable {p q : Prop}

def decidableOfDecidableOfIff (hp : Decidable p) (h : p ↔ q) : Decidable q :=
  if hp : p then isTrue (Iff.mp h hp) else isFalse (Iff.mp (not_iff_not_of_iff h) hp)

def decidableOfDecidableOfEq (hp : Decidable p) (h : p = q) : Decidable q :=
  decidableOfDecidableOfIff hp h.to_iff

protected def Or.byCases [Decidable p] [Decidable q] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hp : p then h₁ hp else if hq : q then h₂ hq else False.rec (Or.elim h hp hq)

end

section

variable {p q : Prop}

instance [Decidable p] [Decidable q] : Decidable (xor p q) :=
  if hp : p then
    if hq : q then isFalse (Or.rec (fun ⟨_, h⟩ => h hq : ¬(p ∧ ¬q)) (fun ⟨_, h⟩ => h hp : ¬(q ∧ ¬p)))
    else isTrue <| Or.inl ⟨hp, hq⟩
  else
    if hq : q then isTrue <| Or.inr ⟨hq, hp⟩
    else isFalse (Or.rec (fun ⟨h, _⟩ => hp h : ¬(p ∧ ¬q)) (fun ⟨h, _⟩ => hq h : ¬(q ∧ ¬p)))

instance existsPropDecidable {p} (P : p → Prop) [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] : Decidable (∃ h, P h) :=
  if h : p then decidableOfDecidableOfIff (DP h) ⟨fun h2 => ⟨h, h2⟩, fun ⟨h', h2⟩ => h2⟩
  else isFalse (mt (fun ⟨h, _⟩ => h) h)

instance forallPropDecidable {p} (P : p → Prop) [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] : Decidable (∀ h, P h) :=
  if h : p then decidableOfDecidableOfIff (DP h) ⟨fun h2 _ => h2, fun al => al h⟩ else isTrue fun h2 => absurd h2 h

end

def IsDecEq {α : Sort u} (p : α → α → Bool) : Prop :=
  ∀ ⦃x y : α⦄, p x y = true → x = y

def IsDecRefl {α : Sort u} (p : α → α → Bool) : Prop :=
  ∀ x, p x x = true

open Decidable

def decidableEqOfBoolPred {α : Sort u} {p : α → α → Bool} (h₁ : IsDecEq p) (h₂ : IsDecRefl p) : DecidableEq α :=
  fun x y : α =>
  if hp : p x y = true then isTrue (h₁ hp)
  else isFalse fun hxy : x = y => absurd (h₂ y) (hxy ▸ hp)

@[inline]
irreducible_def arbitrary (α : Sort u) [Inhabited α] : α :=
  default

instance Prop.inhabited : Inhabited Prop :=
  ⟨True⟩

instance Pi.inhabited (α : Sort u) {β : α → Sort v} [∀ x, Inhabited (β x)] : Inhabited (∀ x, β x) :=
  ⟨fun a => default⟩

instance : Inhabited Bool :=
  ⟨false⟩

instance : Inhabited True :=
  ⟨trivial⟩

instance (priority := 100) nonempty_of_inhabited {α : Sort u} [Inhabited α] : Nonempty α :=
  ⟨default⟩

instance subsingleton_prop (p : Prop) : Subsingleton p :=
  ⟨fun a b => proof_irrel a b⟩

theorem rec_subsingleton {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    [h₃ : ∀ h : p, Subsingleton (h₁ h)] [h₄ : ∀ h : ¬p, Subsingleton (h₂ h)] : Subsingleton (Decidable.recOn h h₂ h₁) :=
  match h with
  | isTrue h => h₃ h
  | isFalse h => h₄ h

@[simp]
theorem if_t_t (c : Prop) [h : Decidable c] {α : Sort u} (t : α) : ite c t t = t :=
  match h with
  | isTrue hc => rfl
  | isFalse hnc => rfl

instance {c t e : Prop} [d_c : Decidable c] [d_t : Decidable t] [d_e : Decidable e] : Decidable (if c then t else e) :=
  match d_c with
  | isTrue hc => d_t
  | isFalse hc => d_e

instance {c : Prop} {t : c → Prop} {e : ¬c → Prop} [d_c : Decidable c] [d_t : ∀ h, Decidable (t h)]
    [d_e : ∀ h, Decidable (e h)] : Decidable (if h : c then t h else e h) :=
  match d_c with
  | isTrue hc => d_t hc
  | isFalse hc => d_e hc

def AsTrue (c : Prop) [Decidable c] : Prop :=
  if c then True else False

def AsFalse (c : Prop) [Decidable c] : Prop :=
  if c then False else True

/-- Universe lifting operation from Sort to Type -/
structure Plift (α : Sort u) : Type u where up ::
  down : α

namespace Plift

-- Bijection between α and plift α
theorem up_down {α : Sort u} : ∀ b : Plift α, up (down b) = b
  | up a => rfl

theorem down_up {α : Sort u} (a : α) : down (up a) = a :=
  rfl

end Plift

section Relation

variable {α : Sort u} {β : Sort v} (r : β → β → Prop)

-- mathport name: «expr ≺ »
local infixl:50 "≺" => r

def Reflexive :=
  ∀ x, x≺x

def Symmetric :=
  ∀ ⦃x y⦄, x≺y → y≺x

def Transitive :=
  ∀ ⦃x y z⦄, x≺y → y≺z → x≺z

def Total :=
  ∀ x y, x≺y ∨ y≺x

theorem mk_equivalence (rfl : Reflexive r) (symm : Symmetric r) (trans : Transitive r) : Equivalence r :=
  ⟨rfl, @symm, @trans⟩

def Irreflexive :=
  ∀ x, ¬x≺x

def AntiSymmetric :=
  ∀ ⦃x y⦄, x≺y → y≺x → x = y

def EmptyRelation := fun a₁ a₂ : α => False

theorem InvImage.trans (f : α → β) (h : Transitive r) : Transitive (InvImage r f) :=
  fun (a₁ a₂ a₃ : α) (h₁ : InvImage r f a₁ a₂) (h₂ : InvImage r f a₂ a₃) => h h₁ h₂

theorem InvImage.irreflexive (f : α → β) (h : Irreflexive r) : Irreflexive (InvImage r f) :=
  fun (a : α) (h₁ : InvImage r f a a) => h (f a) h₁

end Relation

section Binary

variable {α : Type u} {β : Type v}

variable (f : α → α → α)

variable (inv : α → α)

variable (one : α)

-- mathport name: «expr * »
local notation (priority := high) a "*" b => f a b

-- mathport name: «expr ⁻¹»
local notation (priority := high) a "⁻¹" => inv a

variable (g : α → α → α)

-- mathport name: «expr + »
local notation (priority := high) a "+" b => g a b

def Commutative :=
  ∀ a b, (a*b) = b*a

def Associative :=
  ∀ a b c, ((a*b)*c) = a*b*c

def LeftIdentity :=
  ∀ a, (one*a) = a

def RightIdentity :=
  ∀ a, (a*one) = a

def LeftCancelative :=
  ∀ a b c, ((a*b) = a*c) → b = c

def RightCancelative :=
  ∀ a b c, ((a*b) = c*b) → a = c

def LeftDistributive :=
  ∀ a b c, (a*b+c) = (a*b)+a*c

def RightDistributive :=
  ∀ a b c, ((a+b)*c) = (a*c)+b*c

def RightCommutative (h : β → α → β) :=
  ∀ b a₁ a₂, h (h b a₁) a₂ = h (h b a₂) a₁

def LeftCommutative (h : α → β → β) :=
  ∀ a₁ a₂ b, h a₁ (h a₂ b) = h a₂ (h a₁ b)

end Binary

