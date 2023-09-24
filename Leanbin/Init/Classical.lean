/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import Init.Data.Subtype.Basic
import Init.Funext

#align_import init.classical from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

namespace Classical

universe u v

#print Classical.choice /-
/-- The axiom -/
axiom choice {α : Sort u} : Nonempty α → α
#align classical.choice Classical.choice
-/

#print Classical.indefiniteDescription /-
noncomputable irreducible_def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) :
    { x // p x } :=
  choice <|
    let ⟨x, px⟩ := h
    ⟨⟨x, px⟩⟩
#align classical.indefinite_description Classical.indefiniteDescription
-/

#print Classical.choose /-
noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val
#align classical.some Classical.choose
-/

#print Classical.choose_spec /-
theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
#align classical.some_spec Classical.choose_spec
-/

/- Diaconescu's theorem: using function extensionality and propositional extensionality,
   we can get excluded middle from this. -/
section Diaconescu

parameter (p : Prop)

private def U (x : Prop) : Prop :=
  x = True ∨ p

private def V (x : Prop) : Prop :=
  x = False ∨ p

private theorem exU : ∃ x, U x :=
  ⟨True, Or.inl rfl⟩

private theorem exV : ∃ x, V x :=
  ⟨False, Or.inl rfl⟩

private def u : Prop :=
  choose exU

private def v : Prop :=
  choose exV

private theorem u_def : U u :=
  choose_spec exU

private theorem v_def : V v :=
  choose_spec exV

private theorem not_uv_or_p : u ≠ v ∨ p :=
  Or.elim u_def
    (fun hut : u = True =>
      Or.elim v_def
        (fun hvf : v = False =>
          have hne : u ≠ v := hvf.symm ▸ hut.symm ▸ true_ne_false
          Or.inl hne)
        Or.inr)
    Or.inr

private theorem p_implies_uv (hp : p) : u = v :=
  have hpred : U = V :=
    funext fun x : Prop =>
      have hl : x = True ∨ p → x = False ∨ p := fun a => Or.inr hp
      have hr : x = False ∨ p → x = True ∨ p := fun a => Or.inr hp
      show (x = True ∨ p) = (x = False ∨ p) from propext (Iff.intro hl hr)
  have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := hpred ▸ fun exU exV => rfl
  show u = v from h₀ _ _

#print Classical.em /-
theorem em : p ∨ ¬p :=
  Or.elim not_uv_or_p (fun hne : u ≠ v => Or.inr (mt p_implies_uv hne)) Or.inl
#align classical.em Classical.em
-/

end Diaconescu

#print Classical.exists_true_of_nonempty /-
theorem exists_true_of_nonempty {α : Sort u} : Nonempty α → ∃ x : α, True
  | ⟨x⟩ => ⟨x, trivial⟩
#align classical.exists_true_of_nonempty Classical.exists_true_of_nonempty
-/

#print Classical.inhabited_of_nonempty /-
noncomputable def inhabited_of_nonempty {α : Sort u} (h : Nonempty α) : Inhabited α :=
  ⟨choice h⟩
#align classical.inhabited_of_nonempty Classical.inhabited_of_nonempty
-/

#print Classical.inhabited_of_exists /-
noncomputable def inhabited_of_exists {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : Inhabited α :=
  inhabited_of_nonempty (Exists.elim h fun w hw => ⟨w⟩)
#align classical.inhabited_of_exists Classical.inhabited_of_exists
-/

#print Classical.propDecidable /-
/-- All propositions are decidable -/
noncomputable def propDecidable (a : Prop) : Decidable a :=
  choice <| Or.elim (em a) (fun ha => ⟨isTrue ha⟩) fun hna => ⟨isFalse hna⟩
#align classical.prop_decidable Classical.propDecidable
-/

attribute [local instance] prop_decidable

#print Classical.decidableInhabited /-
noncomputable def decidableInhabited (a : Prop) : Inhabited (Decidable a) :=
  ⟨propDecidable a⟩
#align classical.decidable_inhabited Classical.decidableInhabited
-/

attribute [local instance] decidable_inhabited

#print Classical.typeDecidableEq /-
noncomputable def typeDecidableEq (α : Sort u) : DecidableEq α := fun x y => propDecidable (x = y)
#align classical.type_decidable_eq Classical.typeDecidableEq
-/

#print Classical.typeDecidable /-
noncomputable def typeDecidable (α : Sort u) : PSum α (α → False) :=
  match propDecidable (Nonempty α) with
  | is_true hp => PSum.inl (@Inhabited.default _ (inhabited_of_nonempty hp))
  | is_false hn => PSum.inr fun a => absurd (Nonempty.intro a) hn
#align classical.type_decidable Classical.typeDecidable
-/

#print Classical.strongIndefiniteDescription /-
noncomputable irreducible_def strongIndefiniteDescription {α : Sort u} (p : α → Prop)
    (h : Nonempty α) : { x : α // (∃ y : α, p y) → p x } :=
  if hp : ∃ x : α, p x then
    let xp := indefiniteDescription _ hp
    ⟨xp.val, fun h' => xp.property⟩
  else ⟨choice h, fun h => absurd h hp⟩
#align classical.strong_indefinite_description Classical.strongIndefiniteDescription
-/

#print Classical.epsilon /-
/-- The Hilbert epsilon function -/
noncomputable def epsilon {α : Sort u} [h : Nonempty α] (p : α → Prop) : α :=
  (strongIndefiniteDescription p h).val
#align classical.epsilon Classical.epsilon
-/

#print Classical.epsilon_spec_aux /-
theorem epsilon_spec_aux {α : Sort u} (h : Nonempty α) (p : α → Prop) :
    (∃ y, p y) → p (@epsilon α h p) :=
  (strongIndefiniteDescription p h).property
#align classical.epsilon_spec_aux Classical.epsilon_spec_aux
-/

#print Classical.epsilon_spec /-
theorem epsilon_spec {α : Sort u} {p : α → Prop} (hex : ∃ y, p y) :
    p (@epsilon α (nonempty_of_exists hex) p) :=
  epsilon_spec_aux (nonempty_of_exists hex) p hex
#align classical.epsilon_spec Classical.epsilon_spec
-/

#print Classical.epsilon_singleton /-
theorem epsilon_singleton {α : Sort u} (x : α) : (@epsilon α ⟨x⟩ fun y => y = x) = x :=
  @epsilon_spec α (fun y => y = x) ⟨x, rfl⟩
#align classical.epsilon_singleton Classical.epsilon_singleton
-/

#print Classical.axiom_of_choice /-
/-- The axiom of choice -/
theorem axiom_of_choice {α : Sort u} {β : α → Sort v} {r : ∀ x, β x → Prop} (h : ∀ x, ∃ y, r x y) :
    ∃ f : ∀ x, β x, ∀ x, r x (f x) :=
  ⟨_, fun x => choose_spec (h x)⟩
#align classical.axiom_of_choice Classical.axiom_of_choice
-/

#print Classical.skolem /-
theorem skolem {α : Sort u} {b : α → Sort v} {p : ∀ x, b x → Prop} :
    (∀ x, ∃ y, p x y) ↔ ∃ f : ∀ x, b x, ∀ x, p x (f x) :=
  ⟨axiom_of_choice, fun ⟨f, hw⟩ x => ⟨f x, hw x⟩⟩
#align classical.skolem Classical.skolem
-/

#print Classical.prop_complete /-
theorem prop_complete (a : Prop) : a = True ∨ a = False :=
  Or.elim (em a) (fun t => Or.inl (eq_true t)) fun f => Or.inr (eq_false f)
#align classical.prop_complete Classical.prop_complete
-/

section Aux

#print Classical.cases_true_false /-
@[elab_as_elim]
theorem cases_true_false (p : Prop → Prop) (h1 : p True) (h2 : p False) (a : Prop) : p a :=
  Or.elim (prop_complete a) (fun ht : a = True => ht.symm ▸ h1) fun hf : a = False => hf.symm ▸ h2
#align classical.cases_true_false Classical.cases_true_false
-/

#print Classical.cases_on /-
theorem cases_on (a : Prop) {p : Prop → Prop} (h1 : p True) (h2 : p False) : p a :=
  cases_true_false p h1 h2 a
#align classical.cases_on Classical.cases_on
-/

#print by_cases /-
-- this supercedes by_cases in decidable
theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  Decidable.byCases hpq hnpq
#align classical.by_cases by_cases
-/

#print by_contradiction /-
-- this supercedes by_contradiction in decidable
theorem by_contradiction {p : Prop} (h : ¬p → False) : p :=
  Decidable.by_contradiction h
#align classical.by_contradiction by_contradiction
-/

#print Classical.eq_false_or_eq_true /-
theorem eq_false_or_eq_true (a : Prop) : a = False ∨ a = True :=
  (prop_complete a).symm
#align classical.eq_false_or_eq_true Classical.eq_false_or_eq_true
-/

end Aux

end Classical

