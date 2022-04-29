/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import Leanbin.Init.Core

universe u v w

@[simp]
theorem opt_param_eq (α : Sort u) (default : α) : optParam α default = α :=
  rfl

@[inline]
def id {α : Sort u} (a : α) : α :=
  a

def flip {α : Sort u} {β : Sort v} {φ : Sort w} (f : α → β → φ) : β → α → φ := fun b a => f a b

-- implication
def Implies (a b : Prop) :=
  a → b

/-- Implication `→` is transitive. If `P → Q` and `Q → R` then `P → R`. -/
@[trans]
theorem Implies.trans {p q r : Prop} (h₁ : Implies p q) (h₂ : Implies q r) : Implies p r := fun hp => h₂ (h₁ hp)

theorem trivialₓ : True :=
  ⟨⟩

/-- We can't have `a` and `¬a`, that would be absurd!-/
@[inline]
def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : ¬a) : b :=
  False.ndrec b (h₂ h₁)

theorem Not.intro {a : Prop} (h : a → False) : ¬a :=
  h

/-- Modus tollens. If an implication is true, then so is its contrapositive. -/
theorem mt {a b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a := fun ha : a => h₂ (h₁ ha)

-- not
theorem not_false : ¬False :=
  id

def NonContradictory (a : Prop) : Prop :=
  ¬¬a

theorem non_contradictory_intro {a : Prop} (ha : a) : ¬¬a := fun hna : ¬a => absurd ha hna

-- false
@[inline]
def False.elim {C : Sort u} (h : False) : C :=
  False.ndrec C h

-- eq 
-- proof irrelevance is built in
theorem proof_irrelₓ {a : Prop} (h₁ h₂ : a) : h₁ = h₂ :=
  rfl

@[simp]
theorem id.def {α : Sort u} (a : α) : id a = a :=
  rfl

@[inline]
def Eq.mp {α β : Sort u} : α = β → α → β :=
  Eq.recOnₓ

@[inline]
def Eq.mpr {α β : Sort u} : α = β → β → α := fun h₁ h₂ => Eq.recOnₓ (Eq.symm h₁) h₂

@[elab_as_eliminator]
theorem Eq.substr {α : Sort u} {p : α → Prop} {a b : α} (h₁ : b = a) : p a → p b :=
  Eq.subst (Eq.symm h₁)

theorem congr {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α} (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
  Eq.subst h₁ (Eq.subst h₂ rfl)

theorem congr_funₓ {α : Sort u} {β : α → Sort v} {f g : ∀ x, β x} (h : f = g) (a : α) : f a = g a :=
  Eq.subst h (Eq.refl (f a))

theorem congr_argₓ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) : a₁ = a₂ → f a₁ = f a₂ :=
  congr rfl

theorem trans_rel_left {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c :=
  h₂ ▸ h₁

theorem trans_rel_right {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) : r a c :=
  h₁.symm ▸ h₂

theorem of_eq_true {p : Prop} (h : p = True) : p :=
  h.symm ▸ trivialₓ

theorem not_of_eq_false {p : Prop} (h : p = False) : ¬p := fun hp => h ▸ hp

@[inline]
def cast {α β : Sort u} (h : α = β) (a : α) : β :=
  Eq.ndrec a h

theorem cast_proof_irrel {α β : Sort u} (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a :=
  rfl

theorem cast_eq {α : Sort u} (h : α = α) (a : α) : cast h a = a :=
  rfl

-- ne
@[reducible]
def Ne {α : Sort u} (a b : α) :=
  ¬a = b

@[simp]
theorem Ne.def {α : Sort u} (a b : α) : (a ≠ b) = ¬a = b :=
  rfl

namespace Ne

variable {α : Sort u}

variable {a b : α}

theorem intro (h : a = b → False) : a ≠ b :=
  h

theorem elim (h : a ≠ b) : a = b → False :=
  h

theorem irrefl (h : a ≠ a) : False :=
  h rfl

theorem symm (h : a ≠ b) : b ≠ a := fun h₁ : b = a => h h₁.symm

end Ne

theorem false_of_ne {α : Sort u} {a : α} : a ≠ a → False :=
  Ne.irrefl

section

variable {p : Prop}

theorem ne_false_of_self : p → p ≠ False := fun heq : p = False => HEq ▸ hp

theorem ne_true_of_not : ¬p → p ≠ True := fun heq : p = True => (HEq ▸ hnp) trivialₓ

theorem true_ne_false : ¬True = False :=
  ne_false_of_self trivialₓ

end

attribute [refl] HEq.refl

section

variable {α β φ : Sort u} {a a' : α} {b b' : β} {c : φ}

def HEq.elimₓ {α : Sort u} {a : α} {p : α → Sort v} {b : α} (h₁ : HEq a b) : p a → p b :=
  Eq.recOnₓ (eq_of_heq h₁)

theorem HEq.subst {p : ∀ T : Sort u, T → Prop} : HEq a b → p α a → p β b :=
  HEq.recOnₓ

@[symm]
theorem HEq.symm (h : HEq a b) : HEq b a :=
  HEq.recOnₓ h (HEq.refl a)

theorem heq_of_eq (h : a = a') : HEq a a' :=
  Eq.subst h (HEq.refl a)

@[trans]
theorem HEq.trans (h₁ : HEq a b) (h₂ : HEq b c) : HEq a c :=
  HEq.subst h₂ h₁

@[trans]
theorem heq_of_heq_of_eq (h₁ : HEq a b) (h₂ : b = b') : HEq a b' :=
  HEq.trans h₁ (heq_of_eq h₂)

@[trans]
theorem heq_of_eq_of_heq (h₁ : a = a') (h₂ : HEq a' b) : HEq a b :=
  HEq.trans (heq_of_eq h₁) h₂

theorem type_eq_of_heqₓ (h : HEq a b) : α = β :=
  HEq.recOnₓ h (Eq.refl α)

end

theorem eq_rec_heqₓ {α : Sort u} {φ : α → Sort v} : ∀ {a a' : α} h : a = a' p : φ a, HEq (Eq.recOnₓ h p : φ a') p
  | a, _, rfl, p => HEq.refl p

theorem heq_of_eq_rec_leftₓ {α : Sort u} {φ : α → Sort v} :
    ∀ {a a' : α} {p₁ : φ a} {p₂ : φ a'} e : a = a' h₂ : (Eq.recOnₓ e p₁ : φ a') = p₂, HEq p₁ p₂
  | a, _, p₁, p₂, rfl, h => Eq.recOnₓ h (HEq.refl p₁)

theorem heq_of_eq_rec_rightₓ {α : Sort u} {φ : α → Sort v} :
    ∀ {a a' : α} {p₁ : φ a} {p₂ : φ a'} e : a' = a h₂ : p₁ = Eq.recOnₓ e p₂, HEq p₁ p₂
  | a, _, p₁, p₂, rfl, h =>
    have : p₁ = p₂ := h
    this ▸ HEq.refl p₁

theorem of_heq_true {a : Prop} (h : HEq a True) : a :=
  of_eq_true (eq_of_heq h)

theorem eq_rec_compose :
    ∀ {α β φ : Sort u} p₁ : β = φ p₂ : α = β a : α,
      (Eq.recOnₓ p₁ (Eq.recOnₓ p₂ a : β) : φ) = Eq.recOnₓ (Eq.trans p₂ p₁) a
  | α, _, _, rfl, rfl, a => rfl

theorem cast_heq : ∀ {α β : Sort u} h : α = β a : α, HEq (cast h a) a
  | α, _, rfl, a => HEq.refl a

-- and
variable {a b c d : Prop}

theorem And.elimₓ (h₁ : a ∧ b) (h₂ : a → b → c) : c :=
  And.ndrec h₂ h₁

theorem And.swap : a ∧ b → b ∧ a := fun ⟨ha, hb⟩ => ⟨hb, ha⟩

theorem And.symm : a ∧ b → b ∧ a :=
  And.swap

-- or
namespace Or

theorem elim (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → c) : c :=
  Or.ndrec h₂ h₃ h₁

end Or

theorem non_contradictory_em (a : Prop) : ¬¬(a ∨ ¬a) := fun not_em : ¬(a ∨ ¬a) =>
  have neg_a : ¬a := fun pos_a : a => absurd (Or.inl pos_a) not_em
  absurd (Or.inr neg_a) not_em

theorem Or.swap : a ∨ b → b ∨ a :=
  Or.ndrec Or.inr Or.inl

theorem Or.symm : a ∨ b → b ∨ a :=
  Or.swap

-- xor
def Xorₓ (a b : Prop) :=
  a ∧ ¬b ∨ b ∧ ¬a

/-- `iff P Q`, with notation `P ↔ Q`, is the proposition asserting that `P` and `Q` are equivalent,
that is, have the same truth value. -/
-- iff
structure Iff (a b : Prop) : Prop where intro ::
  mp : a → b
  mpr : b → a

theorem Iff.elimₓ : ((a → b) → (b → a) → c) → (a ↔ b) → c :=
  Iff.ndrec

attribute [recursor 5] Iff.elimₓ

theorem Iff.elim_leftₓ : (a ↔ b) → a → b :=
  Iff.mp

theorem Iff.elim_rightₓ : (a ↔ b) → b → a :=
  Iff.mpr

theorem iff_iff_implies_and_implies (a b : Prop) : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
  Iff.intro (fun h => And.intro h.mp h.mpr) fun h => Iff.intro h.left h.right

@[refl]
theorem Iff.refl (a : Prop) : a ↔ a :=
  Iff.intro (fun h => h) fun h => h

theorem Iff.rfl {a : Prop} : a ↔ a :=
  Iff.refl a

@[trans]
theorem Iff.trans (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c :=
  Iff.intro (fun ha => Iff.mp h₂ (Iff.mp h₁ ha)) fun hc => Iff.mpr h₁ (Iff.mpr h₂ hc)

@[symm]
theorem Iff.symm (h : a ↔ b) : b ↔ a :=
  Iff.intro (Iff.elim_rightₓ h) (Iff.elim_leftₓ h)

theorem Iff.comm : (a ↔ b) ↔ (b ↔ a) :=
  Iff.intro Iff.symm Iff.symm

theorem Eq.to_iff {a b : Prop} (h : a = b) : a ↔ b :=
  Eq.recOnₓ h Iff.rfl

theorem neq_of_not_iff {a b : Prop} : ¬(a ↔ b) → a ≠ b := fun h₁ h₂ =>
  have : a ↔ b := Eq.subst h₂ (Iff.refl a)
  absurd this h₁

theorem not_iff_not_of_iff (h₁ : a ↔ b) : ¬a ↔ ¬b :=
  Iff.intro (fun hb : b => hna (Iff.elim_rightₓ h₁ hb)) fun ha : a => hnb (Iff.elim_leftₓ h₁ ha)

theorem of_iff_true (h : a ↔ True) : a :=
  Iff.mp (Iff.symm h) trivialₓ

theorem not_of_iff_false : (a ↔ False) → ¬a :=
  Iff.mp

theorem iff_true_intro (h : a) : a ↔ True :=
  Iff.intro (fun hl => trivialₓ) fun hr => h

theorem iff_false_intro (h : ¬a) : a ↔ False :=
  Iff.intro h (False.ndrec a)

theorem not_non_contradictory_iff_absurd (a : Prop) : ¬¬¬a ↔ ¬a :=
  Iff.intro (fun ha : a => hl (non_contradictory_intro ha)) absurd

theorem imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a → b ↔ c → d :=
  Iff.intro (fun hab hc => Iff.mp h₂ (hab (Iff.mpr h₁ hc))) fun hcd ha => Iff.mpr h₂ (hcd (Iff.mp h₁ ha))

theorem imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : a → b ↔ c → d :=
  Iff.intro
    (fun hab hc =>
      have ha : a := Iff.mpr h₁ hc
      have hb : b := hab ha
      Iff.mp (h₂ hc) hb)
    fun hcd ha =>
    have hc : c := Iff.mp h₁ ha
    have hd : d := hcd hc
    Iff.mpr (h₂ hc) hd

theorem imp_congr_right (h : a → (b ↔ c)) : a → b ↔ a → c :=
  Iff.intro (fun hab ha => Iff.elim_leftₓ (h ha) (hab ha)) fun hab ha => Iff.elim_rightₓ (h ha) (hab ha)

theorem not_not_intro (ha : a) : ¬¬a := fun hna : ¬a => hna ha

theorem not_of_not_not_not (h : ¬¬¬a) : ¬a := fun ha => absurd (not_not_intro ha) h

@[simp]
theorem not_true : ¬True ↔ False :=
  iff_false_intro (not_not_intro trivialₓ)

@[simp]
theorem not_false_iff : ¬False ↔ True :=
  iff_true_intro not_false

@[congr]
theorem not_congr (h : a ↔ b) : ¬a ↔ ¬b :=
  Iff.intro (fun h₁ h₂ => h₁ (Iff.mpr h h₂)) fun h₁ h₂ => h₁ (Iff.mp h h₂)

theorem ne_self_iff_false {α : Sort u} (a : α) : Not (a = a) ↔ False :=
  Iff.intro false_of_ne False.elim

@[simp]
theorem eq_self_iff_true {α : Sort u} (a : α) : a = a ↔ True :=
  iff_true_intro rfl

theorem heq_self_iff_true {α : Sort u} (a : α) : HEq a a ↔ True :=
  iff_true_intro (HEq.refl a)

@[simp]
theorem iff_not_selfₓ (a : Prop) : (a ↔ ¬a) ↔ False :=
  iff_false_intro fun h =>
    have h' : ¬a := fun ha => (Iff.mp h ha) ha
    h' (Iff.mpr h h')

@[simp]
theorem not_iff_selfₓ (a : Prop) : (¬a ↔ a) ↔ False :=
  iff_false_intro fun h =>
    have h' : ¬a := fun ha => (Iff.mpr h ha) ha
    h' (Iff.mp h h')

theorem true_iff_false : (True ↔ False) ↔ False :=
  iff_false_intro fun h => Iff.mp h trivialₓ

theorem false_iff_true : (False ↔ True) ↔ False :=
  iff_false_intro fun h => Iff.mpr h trivialₓ

theorem false_of_true_iff_false : (True ↔ False) → False := fun h => Iff.mp h trivialₓ

theorem false_of_true_eq_false : True = False → False := fun h => h ▸ trivialₓ

theorem true_eq_false_of_false : False → True = False :=
  False.elim

theorem eq_comm {α : Sort u} {a b : α} : a = b ↔ b = a :=
  ⟨Eq.symm, Eq.symm⟩

-- and simp rules
theorem And.imp (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d := fun ⟨ha, hb⟩ => ⟨hac ha, hbd hb⟩

theorem and_implies (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d :=
  And.imp hac hbd

@[congr]
theorem and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d :=
  Iff.intro (And.imp (Iff.mp h₁) (Iff.mp h₂)) (And.imp (Iff.mpr h₁) (Iff.mpr h₂))

theorem and_congr_right (h : a → (b ↔ c)) : a ∧ b ↔ a ∧ c :=
  Iff.intro (fun ⟨ha, hb⟩ => ⟨ha, Iff.elim_leftₓ (h ha) hb⟩) fun ⟨ha, hc⟩ => ⟨ha, Iff.elim_rightₓ (h ha) hc⟩

theorem And.comm : a ∧ b ↔ b ∧ a :=
  Iff.intro And.swap And.swap

theorem and_comm (a b : Prop) : a ∧ b ↔ b ∧ a :=
  And.comm

theorem And.assoc : (a ∧ b) ∧ c ↔ a ∧ b ∧ c :=
  Iff.intro (fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, ⟨hb, hc⟩⟩) fun ⟨ha, ⟨hb, hc⟩⟩ => ⟨⟨ha, hb⟩, hc⟩

theorem and_assoc (a b : Prop) : (a ∧ b) ∧ c ↔ a ∧ b ∧ c :=
  And.assoc

theorem And.left_comm : a ∧ b ∧ c ↔ b ∧ a ∧ c :=
  Iff.trans (Iff.symm And.assoc) (Iff.trans (and_congr And.comm (Iff.refl c)) And.assoc)

theorem and_iff_left {a b : Prop} (hb : b) : a ∧ b ↔ a :=
  Iff.intro And.left fun ha => ⟨ha, hb⟩

theorem and_iff_right {a b : Prop} (ha : a) : a ∧ b ↔ b :=
  Iff.intro And.right (And.intro ha)

@[simp]
theorem and_trueₓ (a : Prop) : a ∧ True ↔ a :=
  and_iff_left trivialₓ

@[simp]
theorem true_andₓ (a : Prop) : True ∧ a ↔ a :=
  and_iff_right trivialₓ

@[simp]
theorem and_falseₓ (a : Prop) : a ∧ False ↔ False :=
  iff_false_intro And.right

@[simp]
theorem false_andₓ (a : Prop) : False ∧ a ↔ False :=
  iff_false_intro And.left

@[simp]
theorem not_and_selfₓ (a : Prop) : ¬a ∧ a ↔ False :=
  iff_false_intro fun h => And.elimₓ h fun h₁ h₂ => absurd h₂ h₁

@[simp]
theorem and_not_selfₓ (a : Prop) : a ∧ ¬a ↔ False :=
  iff_false_intro fun ⟨h₁, h₂⟩ => absurd h₁ h₂

@[simp]
theorem and_selfₓ (a : Prop) : a ∧ a ↔ a :=
  Iff.intro And.left fun h => ⟨h, h⟩

-- or simp rules
theorem Or.imp (h₂ : a → c) (h₃ : b → d) : a ∨ b → c ∨ d :=
  Or.ndrec (fun h => Or.inl (h₂ h)) fun h => Or.inr (h₃ h)

theorem Or.imp_left (h : a → b) : a ∨ c → b ∨ c :=
  Or.imp h id

theorem Or.imp_rightₓ (h : a → b) : c ∨ a → c ∨ b :=
  Or.imp id h

@[congr]
theorem or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∨ b ↔ c ∨ d :=
  Iff.intro (Or.imp (Iff.mp h₁) (Iff.mp h₂)) (Or.imp (Iff.mpr h₁) (Iff.mpr h₂))

theorem Or.comm : a ∨ b ↔ b ∨ a :=
  Iff.intro Or.swap Or.swap

theorem or_comm (a b : Prop) : a ∨ b ↔ b ∨ a :=
  Or.comm

theorem Or.assoc : (a ∨ b) ∨ c ↔ a ∨ b ∨ c :=
  Iff.intro (Or.ndrec (Or.imp_rightₓ Or.inl) fun h => Or.inr (Or.inr h))
    (Or.ndrec (fun h => Or.inl (Or.inl h)) (Or.imp_left Or.inr))

theorem or_assoc (a b : Prop) : (a ∨ b) ∨ c ↔ a ∨ b ∨ c :=
  Or.assoc

theorem Or.left_comm : a ∨ b ∨ c ↔ b ∨ a ∨ c :=
  Iff.trans (Iff.symm Or.assoc) (Iff.trans (or_congr Or.comm (Iff.refl c)) Or.assoc)

theorem or_iff_right_of_imp (ha : a → b) : a ∨ b ↔ b :=
  Iff.intro (Or.ndrec ha id) Or.inr

theorem or_iff_left_of_imp (hb : b → a) : a ∨ b ↔ a :=
  Iff.intro (Or.ndrec id hb) Or.inl

@[simp]
theorem or_trueₓ (a : Prop) : a ∨ True ↔ True :=
  iff_true_intro (Or.inr trivialₓ)

@[simp]
theorem true_orₓ (a : Prop) : True ∨ a ↔ True :=
  iff_true_intro (Or.inl trivialₓ)

@[simp]
theorem or_falseₓ (a : Prop) : a ∨ False ↔ a :=
  Iff.intro (Or.ndrec id False.elim) Or.inl

@[simp]
theorem false_orₓ (a : Prop) : False ∨ a ↔ a :=
  Iff.trans Or.comm (or_falseₓ a)

@[simp]
theorem or_selfₓ (a : Prop) : a ∨ a ↔ a :=
  Iff.intro (Or.ndrec id id) Or.inl

theorem not_orₓ {a b : Prop} : ¬a → ¬b → ¬(a ∨ b)
  | hna, hnb, Or.inl ha => absurd ha hna
  | hna, hnb, Or.inr hb => absurd hb hnb

-- or resolution rulse
theorem Or.resolve_left {a b : Prop} (h : a ∨ b) (na : ¬a) : b :=
  Or.elim h (fun ha => absurd ha na) id

theorem Or.neg_resolve_left {a b : Prop} (h : ¬a ∨ b) (ha : a) : b :=
  Or.elim h (fun na => absurd ha na) id

theorem Or.resolve_right {a b : Prop} (h : a ∨ b) (nb : ¬b) : a :=
  Or.elim h id fun hb => absurd hb nb

theorem Or.neg_resolve_right {a b : Prop} (h : a ∨ ¬b) (hb : b) : a :=
  Or.elim h id fun nb => absurd hb nb

-- iff simp rules
@[simp]
theorem iff_trueₓ (a : Prop) : (a ↔ True) ↔ a :=
  Iff.intro (fun h => Iff.mpr h trivialₓ) iff_true_intro

@[simp]
theorem true_iffₓ (a : Prop) : (True ↔ a) ↔ a :=
  Iff.trans Iff.comm (iff_trueₓ a)

@[simp]
theorem iff_falseₓ (a : Prop) : (a ↔ False) ↔ ¬a :=
  Iff.intro Iff.mp iff_false_intro

@[simp]
theorem false_iffₓ (a : Prop) : (False ↔ a) ↔ ¬a :=
  Iff.trans Iff.comm (iff_falseₓ a)

@[simp]
theorem iff_selfₓ (a : Prop) : (a ↔ a) ↔ True :=
  iff_true_intro Iff.rfl

@[congr]
theorem iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
  (iff_iff_implies_and_implies a b).trans
    ((and_congr (imp_congr h₁ h₂) (imp_congr h₂ h₁)).trans (iff_iff_implies_and_implies c d).symm)

-- implies simp rule
@[simp]
theorem implies_true_iff (α : Sort u) : α → True ↔ True :=
  Iff.intro (fun h => trivialₓ) fun ha h => trivialₓ

theorem false_implies_iff (a : Prop) : False → a ↔ True :=
  Iff.intro (fun h => trivialₓ) fun ha h => False.elim h

theorem true_implies_iff (α : Prop) : True → α ↔ α :=
  Iff.intro (fun h => h trivialₓ) fun h h' => h

/-- The existential quantifier.

To prove a goal of the form `⊢ ∃ x, p x`, you can provide a witness `y` with the tactic `existsi y`.
If you are working in a project that depends on mathlib, then we recommend the `use` tactic
instead.
You'll then be left with the goal `⊢ p y`.

To extract a witness `x` and proof `hx : p x` from a hypothesis `h : ∃ x, p x`,
use the tactic `cases h with x hx`. See also the mathlib tactics `obtain` and `rcases`.
-/
inductive Exists {α : Sort u} (p : α → Prop) : Prop
  | intro (w : α) (h : p w) : Exists

attribute [intro] Exists.intro

-- This is a `def`, so that it can be used as pattern in the equation compiler.
@[matchPattern]
def Exists.introₓ {α : Sort u} {p : α → Prop} (w : α) (h : p w) : ∃ x, p x :=
  ⟨w, h⟩

theorem Exists.elim {α : Sort u} {p : α → Prop} {b : Prop} (h₁ : ∃ x, p x) (h₂ : ∀ a : α, p a → b) : b :=
  Exists.ndrec h₂ h₁

-- exists unique
def ExistsUnique {α : Sort u} (p : α → Prop) :=
  ∃ x, p x ∧ ∀ y, p y → y = x

@[intro]
theorem ExistsUnique.intro {α : Sort u} {p : α → Prop} (w : α) (h₁ : p w) (h₂ : ∀ y, p y → y = w) : ∃! x, p x :=
  Exists.introₓ w ⟨h₁, h₂⟩

@[recursor 4]
theorem ExistsUnique.elim {α : Sort u} {p : α → Prop} {b : Prop} (h₂ : ∃! x, p x)
    (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
  Exists.elim h₂ fun w hw => h₁ w (And.left hw) (And.right hw)

theorem exists_unique_of_exists_of_unique {α : Sort u} {p : α → Prop} (hex : ∃ x, p x)
    (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) : ∃! x, p x :=
  Exists.elim hex fun x px => ExistsUnique.intro x px fun y => fun this : p y => hunique y x this px

theorem exists_of_exists_unique {α : Sort u} {p : α → Prop} (h : ∃! x, p x) : ∃ x, p x :=
  Exists.elim h fun x hx => ⟨x, And.left hx⟩

theorem unique_of_exists_unique {α : Sort u} {p : α → Prop} (h : ∃! x, p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) :
    y₁ = y₂ :=
  ExistsUnique.elim h fun x => fun this : p x => fun unique : ∀ y, p y → y = x =>
    show y₁ = y₂ from Eq.trans (unique _ py₁) (Eq.symm (unique _ py₂))

-- exists, forall, exists unique congruences
@[congr]
theorem forall_congrₓ {α : Sort u} {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∀ a, p a) ↔ ∀ a, q a :=
  Iff.intro (fun p a => Iff.mp (h a) (p a)) fun q a => Iff.mpr (h a) (q a)

theorem exists_imp_exists {α : Sort u} {p q : α → Prop} (h : ∀ a, p a → q a) (p : ∃ a, p a) : ∃ a, q a :=
  Exists.elim p fun a hp => ⟨a, h a hp⟩

@[congr]
theorem exists_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, p a ↔ q a) : Exists p ↔ ∃ a, q a :=
  Iff.intro (exists_imp_exists fun a => Iff.mp (h a)) (exists_imp_exists fun a => Iff.mpr (h a))

@[congr]
theorem exists_unique_congr {α : Sort u} {p₁ p₂ : α → Prop} (h : ∀ x, p₁ x ↔ p₂ x) : ExistsUnique p₁ ↔ ∃! x, p₂ x :=
  --
    exists_congr
    fun x => and_congr (h x) (forall_congrₓ fun y => imp_congr (h y) Iff.rfl)

theorem forall_not_of_not_exists {α : Sort u} {p : α → Prop} : (¬∃ x, p x) → ∀ x, ¬p x := fun hne x hp => hne ⟨x, hp⟩

-- decidable
def Decidable.toBool (p : Prop) [h : Decidable p] : Bool :=
  Decidable.casesOn h (fun h₁ => Bool.false) fun h₂ => Bool.true

export Decidable (isTrue isFalse toBool)

@[simp]
theorem to_bool_true_eq_tt (h : Decidable True) : @toBool True h = tt :=
  Decidable.casesOn h (fun h => False.elim (Iff.mp not_true h)) fun _ => rfl

@[simp]
theorem to_bool_false_eq_ff (h : Decidable False) : @toBool False h = ff :=
  Decidable.casesOn h (fun h => rfl) fun h => False.elim h

instance Decidable.true : Decidable True :=
  isTrue trivialₓ

instance Decidable.false : Decidable False :=
  isFalse not_false

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
@[inline]
def dite {α : Sort u} (c : Prop) [h : Decidable c] : (c → α) → (¬c → α) → α := fun t e => Decidable.recOn h e t

-- if-then-else
@[inline]
def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.recOn h (fun hnc => e) fun hc => t

namespace Decidable

variable {p q : Prop}

def recOnTrue [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : p) (h₄ : h₁ h₃) : Decidable.recOn h h₂ h₁ :=
  Decidable.recOn h (fun h => False.ndrec _ (h h₃)) fun h => h₄

def recOnFalse [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : ¬p) (h₄ : h₂ h₃) :
    Decidable.recOn h h₂ h₁ :=
  Decidable.recOn h (fun h => h₄) fun h => False.ndrec _ (h₃ h)

def byCases {q : Sort u} [φ : Decidable p] : (p → q) → (¬p → q) → q :=
  dite _

/-- Law of Excluded Middle. -/
theorem em (p : Prop) [Decidable p] : p ∨ ¬p :=
  byCases Or.inl Or.inr

theorem by_contradiction [Decidable p] (h : ¬p → False) : p :=
  if h₁ : p then h₁ else False.ndrec _ (h h₁)

theorem of_not_not [Decidable p] : ¬¬p → p := fun hnn => by_contradiction fun hn => absurd hn hnn

theorem not_not_iff p [Decidable p] : ¬¬p ↔ p :=
  Iff.intro of_not_not not_not_intro

theorem not_and_iff_or_not (p q : Prop) [d₁ : Decidable p] [d₂ : Decidable q] : ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
  Iff.intro
    (fun h =>
      match d₁ with
      | is_true h₁ =>
        match d₂ with
        | is_true h₂ => absurd (And.intro h₁ h₂) h
        | is_false h₂ => Or.inr h₂
      | is_false h₁ => Or.inl h₁)
    fun h ⟨hp, hq⟩ => Or.elim h (fun h => h hp) fun h => h hq

theorem not_or_iff_and_not p q [d₁ : Decidable p] [d₂ : Decidable q] : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h =>
      match d₁ with
      | is_true h₁ => False.elim <| h (Or.inl h₁)
      | is_false h₁ =>
        match d₂ with
        | is_true h₂ => False.elim <| h (Or.inr h₂)
        | is_false h₂ => ⟨h₁, h₂⟩)
    fun h => Or.elim h np nq

end Decidable

section

variable {p q : Prop}

def decidableOfDecidableOfIff (hp : Decidable p) (h : p ↔ q) : Decidable q :=
  if hp : p then isTrue (Iff.mp h hp) else isFalse (Iff.mp (not_iff_not_of_iff h) hp)

def decidableOfDecidableOfEq (hp : Decidable p) (h : p = q) : Decidable q :=
  decidableOfDecidableOfIff hp h.to_iff

protected def Or.byCases [Decidable p] [Decidable q] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hp : p then h₁ hp else if hq : q then h₂ hq else False.ndrec _ (Or.elim h hp hq)

end

section

variable {p q : Prop}

instance [Decidable p] [Decidable q] : Decidable (p ∧ q) :=
  if hp : p then if hq : q then isTrue ⟨hp, hq⟩ else isFalse fun h : p ∧ q => hq (And.right h)
  else isFalse fun h : p ∧ q => hp (And.left h)

instance [Decidable p] [Decidable q] : Decidable (p ∨ q) :=
  if hp : p then isTrue (Or.inl hp) else if hq : q then isTrue (Or.inr hq) else isFalse (Or.ndrec hp hq)

instance [Decidable p] : Decidable ¬p :=
  if hp : p then isFalse (absurd hp) else isTrue hp

instance Implies.decidable [Decidable p] [Decidable q] : Decidable (p → q) :=
  if hp : p then if hq : q then isTrue fun h => hq else isFalse fun h : p → q => absurd (h hp) hq
  else isTrue fun h => absurd h hp

instance [Decidable p] [Decidable q] : Decidable (p ↔ q) :=
  if hp : p then if hq : q then isTrue ⟨fun _ => hq, fun _ => hp⟩ else is_false fun h => hq (h.1 hp)
  else if hq : q then is_false fun h => hp (h.2 hq) else is_true <| ⟨fun h => absurd h hp, fun h => absurd h hq⟩

instance [Decidable p] [Decidable q] : Decidable (Xorₓ p q) :=
  if hp : p then
    if hq : q then isFalse (Or.ndrec (fun ⟨_, h⟩ => h hq : ¬(p ∧ ¬q)) (fun ⟨_, h⟩ => h hp : ¬(q ∧ ¬p)))
    else is_true <| Or.inl ⟨hp, hq⟩
  else
    if hq : q then is_true <| Or.inr ⟨hq, hp⟩
    else isFalse (Or.ndrec (fun ⟨h, _⟩ => hp h : ¬(p ∧ ¬q)) (fun ⟨h, _⟩ => hq h : ¬(q ∧ ¬p)))

instance existsPropDecidable {p} (P : p → Prop) [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] : Decidable (∃ h, P h) :=
  if h : p then decidableOfDecidableOfIff (DP h) ⟨fun h2 => ⟨h, h2⟩, fun ⟨h', h2⟩ => h2⟩
  else isFalse (mt (fun ⟨h, _⟩ => h) h)

instance forallPropDecidable {p} (P : p → Prop) [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] : Decidable (∀ h, P h) :=
  if h : p then decidableOfDecidableOfIff (DP h) ⟨fun h2 _ => h2, fun al => al h⟩ else isTrue fun h2 => absurd h2 h

end

instance {α : Sort u} [DecidableEq α] (a b : α) : Decidable (a ≠ b) :=
  Implies.decidable

theorem Bool.ff_ne_tt : ff = tt → False :=
  fun.

def IsDecEq {α : Sort u} (p : α → α → Bool) : Prop :=
  ∀ ⦃x y : α⦄, p x y = tt → x = y

def IsDecRefl {α : Sort u} (p : α → α → Bool) : Prop :=
  ∀ x, p x x = tt

open Decidable

instance : DecidableEq Bool
  | ff, ff => isTrue rfl
  | ff, tt => isFalse Bool.ff_ne_tt
  | tt, ff => isFalse (Ne.symm Bool.ff_ne_tt)
  | tt, tt => isTrue rfl

def decidableEqOfBoolPred {α : Sort u} {p : α → α → Bool} (h₁ : IsDecEq p) (h₂ : IsDecRefl p) : DecidableEq α :=
  fun x y : α =>
  if hp : p x y = tt then isTrue (h₁ hp)
  else isFalse fun hxy : x = y => absurd (h₂ y) (@Eq.recOnₓ _ _ (fun z => ¬p z y = tt) _ hxy hp)

theorem decidable_eq_inl_refl {α : Sort u} [h : DecidableEq α] (a : α) : h a a = isTrue (Eq.refl a) :=
  match h a a with
  | is_true e => rfl
  | is_false n => absurd rfl n

theorem decidable_eq_inr_neg {α : Sort u} [h : DecidableEq α] {a b : α} : ∀ n : a ≠ b, h a b = isFalse n := fun n =>
  match h a b with
  | is_true e => absurd e n
  | is_false n₁ => proof_irrelₓ n n₁ ▸ Eq.refl (isFalse n)

-- inhabited
class Inhabited (α : Sort u) where
  default : α

export Inhabited (default)

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
  ⟨trivialₓ⟩

class inductive Nonempty (α : Sort u) : Prop
  | intro (val : α) : Nonempty

protected theorem Nonempty.elimₓ {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : α → p) : p :=
  Nonempty.ndrec h₂ h₁

instance (priority := 100) nonempty_of_inhabited {α : Sort u} [Inhabited α] : Nonempty α :=
  ⟨default⟩

theorem nonempty_of_exists {α : Sort u} {p : α → Prop} : (∃ x, p x) → Nonempty α
  | ⟨w, h⟩ => ⟨w⟩

-- subsingleton
class inductive Subsingleton (α : Sort u) : Prop
  | intro (h : ∀ a b : α, a = b) : Subsingleton

protected theorem Subsingleton.elimₓ {α : Sort u} [h : Subsingleton α] : ∀ a b : α, a = b :=
  Subsingleton.ndrec (fun p => p) h

protected theorem Subsingleton.helimₓ {α β : Sort u} [h : Subsingleton α] (h : α = β) : ∀ a : α b : β, HEq a b :=
  Eq.recOnₓ h fun a b : α => heq_of_eq (Subsingleton.elimₓ a b)

instance subsingleton_prop (p : Prop) : Subsingleton p :=
  ⟨fun a b => proof_irrelₓ a b⟩

instance (p : Prop) : Subsingleton (Decidable p) :=
  Subsingleton.intro fun d₁ =>
    match d₁ with
    | is_true t₁ => fun d₂ =>
      match d₂ with
      | is_true t₂ => Eq.recOnₓ (proof_irrelₓ t₁ t₂) rfl
      | is_false f₂ => absurd t₁ f₂
    | is_false f₁ => fun d₂ =>
      match d₂ with
      | is_true t₂ => absurd t₂ f₁
      | is_false f₂ => Eq.recOnₓ (proof_irrelₓ f₁ f₂) rfl

protected theorem rec_subsingleton {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    [h₃ : ∀ h : p, Subsingleton (h₁ h)] [h₄ : ∀ h : ¬p, Subsingleton (h₂ h)] : Subsingleton (Decidable.recOn h h₂ h₁) :=
  match h with
  | is_true h => h₃ h
  | is_false h => h₄ h

theorem if_pos {c : Prop} [h : Decidable c] (hc : c) {α : Sort u} {t e : α} : ite c t e = t :=
  match h with
  | is_true hc => rfl
  | is_false hnc => absurd hc hnc

theorem if_neg {c : Prop} [h : Decidable c] (hnc : ¬c) {α : Sort u} {t e : α} : ite c t e = e :=
  match h with
  | is_true hc => absurd hc hnc
  | is_false hnc => rfl

@[simp]
theorem if_t_t (c : Prop) [h : Decidable c] {α : Sort u} (t : α) : ite c t t = t :=
  match h with
  | is_true hc => rfl
  | is_false hnc => rfl

theorem implies_of_if_pos {c t e : Prop} [Decidable c] (h : ite c t e) : c → t := fun hc =>
  Eq.recOnₓ (if_pos hc : ite c t e = t) h

theorem implies_of_if_neg {c t e : Prop} [Decidable c] (h : ite c t e) : ¬c → e := fun hnc =>
  Eq.recOnₓ (if_neg hnc : ite c t e = e) h

theorem if_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c] {x y u v : α} (h_c : b ↔ c)
    (h_t : c → x = u) (h_e : ¬c → y = v) : ite b x y = ite c u v :=
  match dec_b, dec_c with
  | is_false h₁, is_false h₂ => h_e h₂
  | is_true h₁, is_true h₂ => h_t h₂
  | is_false h₁, is_true h₂ => absurd h₂ (Iff.mp (not_iff_not_of_iff h_c) h₁)
  | is_true h₁, is_false h₂ => absurd h₁ (Iff.mpr (not_iff_not_of_iff h_c) h₂)

theorem if_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c] {x y u v : α} (h_c : b ↔ c)
    (h_t : x = u) (h_e : y = v) : ite b x y = ite c u v :=
  @if_ctx_congr α b c dec_b dec_c x y u v h_c (fun h => h_t) fun h => h_e

@[simp]
theorem if_true {α : Sort u} {h : Decidable True} (t e : α) : @ite α True h t e = t :=
  if_pos trivialₓ

@[simp]
theorem if_false {α : Sort u} {h : Decidable False} (t e : α) : @ite α False h t e = e :=
  if_neg not_false

theorem if_ctx_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c] (h_c : b ↔ c)
    (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c u v :=
  match dec_b, dec_c with
  | is_false h₁, is_false h₂ => h_e h₂
  | is_true h₁, is_true h₂ => h_t h₂
  | is_false h₁, is_true h₂ => absurd h₂ (Iff.mp (not_iff_not_of_iff h_c) h₁)
  | is_true h₁, is_false h₂ => absurd h₁ (Iff.mpr (not_iff_not_of_iff h_c) h₂)

@[congr]
theorem if_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c] (h_c : b ↔ c) (h_t : x ↔ u)
    (h_e : y ↔ v) : ite b x y ↔ ite c u v :=
  if_ctx_congr_prop h_c (fun h => h_t) fun h => h_e

theorem if_ctx_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] (h_c : b ↔ c) (h_t : c → (x ↔ u))
    (h_e : ¬c → (y ↔ v)) : ite b x y ↔ @ite Prop c (decidableOfDecidableOfIff dec_b h_c) u v :=
  @if_ctx_congr_prop b c x y u v dec_b (decidableOfDecidableOfIff dec_b h_c) h_c h_t h_e

@[congr]
theorem if_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
    ite b x y ↔ @ite Prop c (decidableOfDecidableOfIff dec_b h_c) u v :=
  @if_ctx_simp_congr_prop b c x y u v dec_b h_c (fun h => h_t) fun h => h_e

@[simp]
theorem dif_pos {c : Prop} [h : Decidable c] (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = t hc :=
  match h with
  | is_true hc => rfl
  | is_false hnc => absurd hc hnc

@[simp]
theorem dif_neg {c : Prop} [h : Decidable c] (hnc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = e hnc :=
  match h with
  | is_true hc => absurd hc hnc
  | is_false hnc => rfl

@[congr]
theorem dif_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c] {x : b → α} {u : c → α}
    {y : ¬b → α} {v : ¬c → α} (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_iff_not_of_iff h_c) h) = v h) : @dite α b dec_b x y = @dite α c dec_c u v :=
  match dec_b, dec_c with
  | is_false h₁, is_false h₂ => h_e h₂
  | is_true h₁, is_true h₂ => h_t h₂
  | is_false h₁, is_true h₂ => absurd h₂ (Iff.mp (not_iff_not_of_iff h_c) h₁)
  | is_true h₁, is_false h₂ => absurd h₁ (Iff.mpr (not_iff_not_of_iff h_c) h₂)

theorem dif_ctx_simp_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] {x : b → α} {u : c → α} {y : ¬b → α}
    {v : ¬c → α} (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
    @dite α b dec_b x y = @dite α c (decidableOfDecidableOfIff dec_b h_c) u v :=
  @dif_ctx_congr α b c dec_b (decidableOfDecidableOfIff dec_b h_c) x u y v h_c h_t h_e

-- Remark: dite and ite are "defally equal" when we ignore the proofs.
theorem dif_eq_if (c : Prop) [h : Decidable c] {α : Sort u} (t : α) (e : α) :
    (dite c (fun h => t) fun h => e) = ite c t e :=
  match h with
  | is_true hc => rfl
  | is_false hnc => rfl

instance {c t e : Prop} [d_c : Decidable c] [d_t : Decidable t] [d_e : Decidable e] : Decidable (if c then t else e) :=
  match d_c with
  | is_true hc => d_t
  | is_false hc => d_e

instance {c : Prop} {t : c → Prop} {e : ¬c → Prop} [d_c : Decidable c] [d_t : ∀ h, Decidable (t h)]
    [d_e : ∀ h, Decidable (e h)] : Decidable (if h : c then t h else e h) :=
  match d_c with
  | is_true hc => d_t hc
  | is_false hc => d_e hc

def AsTrue (c : Prop) [Decidable c] : Prop :=
  if c then True else False

def AsFalse (c : Prop) [Decidable c] : Prop :=
  if c then False else True

theorem of_as_true {c : Prop} [h₁ : Decidable c] (h₂ : AsTrue c) : c :=
  match h₁, h₂ with
  | is_true h_c, h₂ => h_c
  | is_false h_c, h₂ => False.elim h₂

/-- Universe lifting operation -/
structure ULift.{r, s} (α : Type s) : Type max s r where up ::
  down : α

namespace ULift

-- Bijection between α and ulift.{v} α
theorem up_down {α : Type u} : ∀ b : ULift.{v} α, up (down b) = b
  | up a => rfl

theorem down_up {α : Type u} (a : α) : down (up.{v} a) = a :=
  rfl

end ULift

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

-- Equalities for rewriting let-expressions
theorem let_value_eq {α : Sort u} {β : Sort v} {a₁ a₂ : α} (b : α → β) :
    a₁ = a₂ →
      (let x : α := a₁
        b x) =
        let x : α := a₂
        b x :=
  fun h => Eq.recOnₓ h rfl

theorem let_value_heqₓ {α : Sort v} {β : α → Sort u} {a₁ a₂ : α} (b : ∀ x : α, β x) :
    a₁ = a₂ →
      HEq
        (let x : α := a₁
        b x)
        (let x : α := a₂
        b x) :=
  fun h => Eq.recOnₓ h (HEq.refl (b a₁))

theorem let_body_eqₓ {α : Sort v} {β : α → Sort u} (a : α) {b₁ b₂ : ∀ x : α, β x} :
    (∀ x, b₁ x = b₂ x) →
      (let x : α := a
        b₁ x) =
        let x : α := a
        b₂ x :=
  fun h => h a

theorem let_eqₓ {α : Sort v} {β : Sort u} {a₁ a₂ : α} {b₁ b₂ : α → β} :
    a₁ = a₂ →
      (∀ x, b₁ x = b₂ x) →
        (let x : α := a₁
          b₁ x) =
          let x : α := a₂
          b₂ x :=
  fun h₁ h₂ => Eq.recOnₓ h₁ (h₂ a₁)

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

def Equivalenceₓ :=
  Reflexive r ∧ Symmetric r ∧ Transitive r

def Total :=
  ∀ x y, x≺y ∨ y≺x

theorem mk_equivalence (rfl : Reflexive r) (symm : Symmetric r) (trans : Transitive r) : Equivalenceₓ r :=
  ⟨rfl, symm, trans⟩

def Irreflexive :=
  ∀ x, ¬x≺x

def AntiSymmetric :=
  ∀ ⦃x y⦄, x≺y → y≺x → x = y

def EmptyRelation := fun a₁ a₂ : α => False

def Subrelation (q r : β → β → Prop) :=
  ∀ ⦃x y⦄, q x y → r x y

def InvImage (f : α → β) : α → α → Prop := fun a₁ a₂ => f a₁≺f a₂

theorem InvImage.trans (f : α → β) (h : Transitive r) : Transitive (InvImage r f) := fun h₂ : InvImage r f a₂ a₃ =>
  h h₁ h₂

theorem InvImage.irreflexive (f : α → β) (h : Irreflexive r) : Irreflexive (InvImage r f) :=
  fun h₁ : InvImage r f a a => h (f a) h₁

inductive Tc {α : Sort u} (r : α → α → Prop) : α → α → Prop
  | base : ∀ a b, r a b → Tc a b
  | trans : ∀ a b c, Tc a b → Tc b c → Tc a c

end Relation

section Binary

variable {α : Type u} {β : Type v}

variable (f : α → α → α)

variable (inv : α → α)

variable (one : α)

-- mathport name: «expr * »
local notation a "*" b => f a b

-- mathport name: «expr ⁻¹»
local notation a "⁻¹" => inv a

variable (g : α → α → α)

-- mathport name: «expr + »
local notation a "+" b => g a b

def Commutative :=
  ∀ a b, (a*b) = b*a

def Associative :=
  ∀ a b c, ((a*b)*c) = a*b*c

def LeftIdentity :=
  ∀ a, (one*a) = a

def RightIdentity :=
  ∀ a, (a*one) = a

def RightInverse :=
  ∀ a, (a*a⁻¹) = one

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

theorem left_comm : Commutative f → Associative f → LeftCommutative f := fun hcomm hassoc => fun a b c =>
  calc
    (a*b*c) = (a*b)*c := Eq.symm (hassoc a b c)
    _ = (b*a)*c := hcomm a b ▸ rfl
    _ = b*a*c := hassoc b a c
    

theorem right_comm : Commutative f → Associative f → RightCommutative f := fun hcomm hassoc => fun a b c =>
  calc
    ((a*b)*c) = a*b*c := hassoc a b c
    _ = a*c*b := hcomm b c ▸ rfl
    _ = (a*c)*b := Eq.symm (hassoc a c b)
    

end Binary

