prelude 
import Leanbin.Init.Data.Subtype.Basic 
import Leanbin.Init.Funext

namespace Classical

universe u v

axiom choice {α : Sort u} : Nonempty α → α

@[irreducible]
noncomputable def indefinite_description {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : { x // p x } :=
  choice$
    let ⟨x, px⟩ := h
    ⟨⟨x, px⟩⟩

noncomputable def some {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefinite_description p h).val

theorem some_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (some h) :=
  (indefinite_description p h).property

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

private theorem u : Prop :=
  some exU

private theorem v : Prop :=
  some exV

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
    funext
      fun x : Prop =>
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

noncomputable def inhabited_of_nonempty {α : Sort u} (h : Nonempty α) : Inhabited α :=
  ⟨choice h⟩

noncomputable def inhabited_of_exists {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : Inhabited α :=
  inhabited_of_nonempty (Exists.elim h fun w hw => ⟨w⟩)

noncomputable def prop_decidable (a : Prop) : Decidable a :=
  choice$ Or.elim (em a) (fun ha => ⟨is_true ha⟩) fun hna => ⟨is_false hna⟩

attribute [local instance] prop_decidable

noncomputable def decidable_inhabited (a : Prop) : Inhabited (Decidable a) :=
  ⟨prop_decidable a⟩

attribute [local instance] decidable_inhabited

noncomputable def type_decidable_eq (α : Sort u) : DecidableEq α :=
  fun x y => prop_decidable (x = y)

noncomputable def type_decidable (α : Sort u) : Psum α (α → False) :=
  match prop_decidable (Nonempty α) with 
  | is_true hp => Psum.inl (@Inhabited.default _ (inhabited_of_nonempty hp))
  | is_false hn => Psum.inr fun a => absurd (Nonempty.intro a) hn

@[irreducible]
noncomputable def strong_indefinite_description {α : Sort u} (p : α → Prop) (h : Nonempty α) :
  { x : α // (∃ y : α, p y) → p x } :=
  if hp : ∃ x : α, p x then
    let xp := indefinite_description _ hp
    ⟨xp.val, fun h' => xp.property⟩
  else ⟨choice h, fun h => absurd h hp⟩

noncomputable def epsilon {α : Sort u} [h : Nonempty α] (p : α → Prop) : α :=
  (strong_indefinite_description p h).val

theorem epsilon_spec_aux {α : Sort u} (h : Nonempty α) (p : α → Prop) : (∃ y, p y) → p (@epsilon α h p) :=
  (strong_indefinite_description p h).property

theorem epsilon_spec {α : Sort u} {p : α → Prop} (hex : ∃ y, p y) : p (@epsilon α (nonempty_of_exists hex) p) :=
  epsilon_spec_aux (nonempty_of_exists hex) p hex

theorem epsilon_singleton {α : Sort u} (x : α) : (@epsilon α ⟨x⟩ fun y => y = x) = x :=
  @epsilon_spec α (fun y => y = x) ⟨x, rfl⟩

theorem axiom_of_choice {α : Sort u} {β : α → Sort v} {r : ∀ x, β x → Prop} (h : ∀ x, ∃ y, r x y) :
  ∃ f : ∀ x, β x, ∀ x, r x (f x) :=
  ⟨_, fun x => some_spec (h x)⟩

theorem skolem {α : Sort u} {b : α → Sort v} {p : ∀ x, b x → Prop} :
  (∀ x, ∃ y, p x y) ↔ ∃ f : ∀ x, b x, ∀ x, p x (f x) :=
  ⟨axiom_of_choice, fun ⟨f, hw⟩ x => ⟨f x, hw x⟩⟩

theorem prop_complete (a : Prop) : a = True ∨ a = False :=
  Or.elim (em a) (fun t => Or.inl (eq_true_intro t)) fun f => Or.inr (eq_false_intro f)

section Aux

@[elab_as_eliminator]
theorem cases_true_false (p : Prop → Prop) (h1 : p True) (h2 : p False) (a : Prop) : p a :=
  Or.elim (prop_complete a) (fun ht : a = True => ht.symm ▸ h1) fun hf : a = False => hf.symm ▸ h2

theorem cases_on (a : Prop) {p : Prop → Prop} (h1 : p True) (h2 : p False) : p a :=
  cases_true_false p h1 h2 a

theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  Decidable.byCases hpq hnpq

theorem by_contradiction {p : Prop} (h : ¬p → False) : p :=
  Decidable.by_contradiction h

theorem eq_false_or_eq_true (a : Prop) : a = False ∨ a = True :=
  (prop_complete a).symm

end Aux

end Classical

