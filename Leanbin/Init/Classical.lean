/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import Leanbin.Init.Data.Subtype.Basic
import Leanbin.Init.Funext

namespace Classical

universe u v

-- the axiom
axiom choice {α : Sort u} : Nonempty α → α

noncomputable irreducible_def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : { x // p x } :=
  choice <|
    let ⟨x, px⟩ := h
    ⟨⟨x, px⟩⟩

noncomputable def some {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem some_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (some h) :=
  (indefiniteDescription p h).property

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

/- TODO(Leo): check why the code generator is not ignoring (some exU)
   when we mark u as def. -/
private theorem u : Prop :=
  some exU

private theorem v : Prop :=
  some exV

-- ././Mathport/Syntax/Translate/Basic.lean:210:40: warning: unsupported option type_context.unfold_lemmas
set_option type_context.unfold_lemmas true

private theorem u_def : U u :=
  some_spec exU

private theorem v_def : V v :=
  some_spec exV

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
  have h₀ : ∀ exU exV, @some _ U exU = @some _ V exV := hpred ▸ fun exU exV => rfl
  show u = v from h₀ _ _

theorem em : p ∨ ¬p :=
  Or.elim not_uv_or_p (fun hne : u ≠ v => Or.inr (mt p_implies_uv hne)) Or.inl

end Diaconescu

theorem exists_true_of_nonempty {α : Sort u} : Nonempty α → ∃ x : α, True
  | ⟨x⟩ => ⟨x, trivialₓ⟩

noncomputable def inhabitedOfNonempty {α : Sort u} (h : Nonempty α) : Inhabited α :=
  ⟨choice h⟩

noncomputable def inhabitedOfExists {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : Inhabited α :=
  inhabitedOfNonempty (Exists.elim h fun w hw => ⟨w⟩)

-- all propositions are decidable
noncomputable def propDecidable (a : Prop) : Decidable a :=
  choice <| Or.elim (em a) (fun ha => ⟨isTrue ha⟩) fun hna => ⟨isFalse hna⟩

attribute [local instance] prop_decidable

noncomputable def decidableInhabited (a : Prop) : Inhabited (Decidable a) :=
  ⟨propDecidable a⟩

attribute [local instance] decidable_inhabited

noncomputable def typeDecidableEq (α : Sort u) : DecidableEq α := fun x y => propDecidable (x = y)

noncomputable def typeDecidable (α : Sort u) : PSum α (α → False) :=
  match propDecidable (Nonempty α) with
  | is_true hp => PSum.inl (@Inhabited.default _ (inhabitedOfNonempty hp))
  | is_false hn => PSum.inr fun a => absurd (Nonempty.intro a) hn

noncomputable irreducible_def strongIndefiniteDescription {α : Sort u} (p : α → Prop) (h : Nonempty α) :
  { x : α // (∃ y : α, p y) → p x } :=
  if hp : ∃ x : α, p x then
    let xp := indefiniteDescription _ hp
    ⟨xp.val, fun h' => xp.property⟩
  else ⟨choice h, fun h => absurd h hp⟩

-- the Hilbert epsilon function
noncomputable def epsilon {α : Sort u} [h : Nonempty α] (p : α → Prop) : α :=
  (strongIndefiniteDescription p h).val

theorem epsilon_spec_aux {α : Sort u} (h : Nonempty α) (p : α → Prop) : (∃ y, p y) → p (@epsilon α h p) :=
  (strongIndefiniteDescription p h).property

theorem epsilon_spec {α : Sort u} {p : α → Prop} (hex : ∃ y, p y) : p (@epsilon α (nonempty_of_exists hex) p) :=
  epsilon_spec_aux (nonempty_of_exists hex) p hex

theorem epsilon_singleton {α : Sort u} (x : α) : (@epsilon α ⟨x⟩ fun y => y = x) = x :=
  @epsilon_spec α (fun y => y = x) ⟨x, rfl⟩

-- the axiom of choice
theorem axiom_of_choice {α : Sort u} {β : α → Sort v} {r : ∀ x, β x → Prop} (h : ∀ x, ∃ y, r x y) :
    ∃ f : ∀ x, β x, ∀ x, r x (f x) :=
  ⟨_, fun x => some_spec (h x)⟩

theorem skolem {α : Sort u} {b : α → Sort v} {p : ∀ x, b x → Prop} :
    (∀ x, ∃ y, p x y) ↔ ∃ f : ∀ x, b x, ∀ x, p x (f x) :=
  ⟨axiom_of_choice, fun x => ⟨f x, hw x⟩⟩

theorem prop_complete (a : Prop) : a = True ∨ a = False :=
  Or.elim (em a) (fun t => Or.inl (eq_true_intro t)) fun f => Or.inr (eq_false_intro f)

section Aux

@[elab_as_eliminator]
theorem cases_true_false (p : Prop → Prop) (h1 : p True) (h2 : p False) (a : Prop) : p a :=
  Or.elim (prop_complete a) (fun ht : a = True => ht.symm ▸ h1) fun hf : a = False => hf.symm ▸ h2

theorem cases_on (a : Prop) {p : Prop → Prop} (h1 : p True) (h2 : p False) : p a :=
  cases_true_false p h1 h2 a

-- this supercedes by_cases in decidable
theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  Decidable.byCases hpq hnpq

-- this supercedes by_contradiction in decidable
theorem by_contradiction {p : Prop} (h : ¬p → False) : p :=
  Decidable.by_contradiction h

theorem eq_false_or_eq_true (a : Prop) : a = False ∨ a = True :=
  (prop_complete a).symm

end Aux

end Classical

