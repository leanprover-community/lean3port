/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Quotient types.

! This file was ported from Lean 3 source module init.data.quot
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Sigma.Basic
import Leanbin.Init.Logic
import Leanbin.Init.Propext
import Leanbin.Init.Data.Setoid

-- We import propext here, otherwise we would need a quot.lift for propositions.
universe u v

-- iff can now be used to do substitutions in a calculation
@[subst]
theorem iff_subst {a b : Prop} {p : Prop → Prop} (h₁ : a ↔ b) (h₂ : p a) : p b :=
  Eq.subst (propext h₁) h₂
#align iff_subst iff_subst

namespace Quot

#print Quot.sound /-
axiom sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
#align quot.sound Quot.sound
-/

attribute [elab_as_elim] lift ind

/- warning: quot.lift_beta -> Quot.lift_mk is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {r : α -> α -> Prop} {β : Sort.{u2}} (f : α -> β) (c : forall (a : α) (b : α), (r a b) -> (Eq.{u2} β (f a) (f b))) (a : α), Eq.{u2} β (Quot.lift.{u1, u2} α (fun (a : α) (b : α) => r a b) β f c (Quot.mk.{u1} α r a)) (f a)
but is expected to have type
  forall {α : Sort.{u1}} {r : Sort.{u2}} {β : α -> α -> Prop} (f : α -> r) (c : forall (a : α) (b : α), (β a b) -> (Eq.{u2} r (f a) (f b))) (a : α), Eq.{u2} r (Quot.lift.{u1, u2} α (fun (a : α) (b : α) => β a b) r f c (Quot.mk.{u1} α β a)) (f a)
Case conversion may be inaccurate. Consider using '#align quot.lift_beta Quot.lift_mkₓ'. -/
protected theorem lift_mk {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)
    (c : ∀ a b, r a b → f a = f b) (a : α) : lift f c (Quot.mk r a) = f a :=
  rfl
#align quot.lift_beta Quot.lift_mk

protected theorem ind_beta {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop}
    (p : ∀ a, β (Quot.mk r a)) (a : α) : (ind p (Quot.mk r a) : β (Quot.mk r a)) = p a :=
  rfl
#align quot.ind_beta Quot.ind_beta

#print Quot.liftOn /-
@[reducible, elab_as_elim]
protected def liftOn {α : Sort u} {β : Sort v} {r : α → α → Prop} (q : Quot r) (f : α → β)
    (c : ∀ a b, r a b → f a = f b) : β :=
  lift f c q
#align quot.lift_on Quot.liftOn
-/

#print Quot.induction_on /-
@[elab_as_elim]
protected theorem induction_on {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r)
    (h : ∀ a, β (Quot.mk r a)) : β q :=
  ind h q
#align quot.induction_on Quot.induction_on
-/

#print Quot.exists_rep /-
theorem exists_rep {α : Sort u} {r : α → α → Prop} (q : Quot r) : ∃ a : α, Quot.mk r a = q :=
  Quot.induction_on q fun a => ⟨a, rfl⟩
#align quot.exists_rep Quot.exists_rep
-/

section

variable {α : Sort u}

variable {r : α → α → Prop}

variable {β : Quot r → Sort v}

-- mathport name: «expr⟦ ⟧»
local notation:arg "⟦" a "⟧" => Quot.mk r a

#print Quot.indep /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible []))]
        "]")]
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `indep [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.forall "∀" [`a] [] "," (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")]))]
         []
         ")")
        (Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       [(Term.typeSpec ":" (Term.app `PSigma [`β]))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "," (Term.app `f [`a])]
        "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧") "," (Term.app `f [`a])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Quot.Init.Data.Quot.term⟦_⟧._@.Init.Data.Quot._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ reducible ] protected def indep ( f : ∀ a , β ⟦ a ⟧ ) ( a : α ) : PSigma β := ⟨ ⟦ a ⟧ , f a ⟩
#align quot.indep Quot.indep
-/

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `indep_coherent [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.forall "∀" [`a] [] "," (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")
            (Term.explicitBinder "(" [`p] [":" (Term.app `r [`a `b])] [] ")")]
           []
           ","
           («term_=_»
            (Term.typeAscription
             "("
             (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
             ":"
             [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
             ")")
            "="
            (Term.app `f [`b])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`a `b]
         []
         ","
         (Term.arrow
          (Term.app `r [`a `b])
          "→"
          («term_=_» (Term.app `Quot.indep [`f `a]) "=" (Term.app `Quot.indep [`f `b]))))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`a `b `e]
         []
         "=>"
         (Term.app `PSigma.eq [(Term.app `sound [`e]) (Term.app `h [`a `b `e])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `b `e]
        []
        "=>"
        (Term.app `PSigma.eq [(Term.app `sound [`e]) (Term.app `h [`a `b `e])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `PSigma.eq [(Term.app `sound [`e]) (Term.app `h [`a `b `e])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`a `b `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`a `b `e]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `sound [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sound
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `sound [`e]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PSigma.eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`a `b]
       []
       ","
       (Term.arrow
        (Term.app `r [`a `b])
        "→"
        («term_=_» (Term.app `Quot.indep [`f `a]) "=" (Term.app `Quot.indep [`f `b]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `r [`a `b])
       "→"
       («term_=_» (Term.app `Quot.indep [`f `a]) "=" (Term.app `Quot.indep [`f `b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `Quot.indep [`f `a]) "=" (Term.app `Quot.indep [`f `b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Quot.indep [`f `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.indep
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `Quot.indep [`f `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.indep
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `r [`a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")
        (Term.explicitBinder "(" [`p] [":" (Term.app `r [`a `b])] [] ")")]
       []
       ","
       («term_=_»
        (Term.typeAscription
         "("
         (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
         ":"
         [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
         ")")
        "="
        (Term.app `f [`b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
        ":"
        [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
        ")")
       "="
       (Term.app `f [`b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
       ":"
       [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Quot.Init.Data.Quot.term⟦_⟧._@.Init.Data.Quot._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    indep_coherent
    ( f : ∀ a , β ⟦ a ⟧ )
        ( h : ∀ ( a b : α ) ( p : r a b ) , ( Eq.ndrec f a sound p : β ⟦ b ⟧ ) = f b )
      : ∀ a b , r a b → Quot.indep f a = Quot.indep f b
    := fun a b e => PSigma.eq sound e h a b e
#align quot.indep_coherent Quot.indep_coherent

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lift_indep_pr1 [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.forall "∀" [`a] [] "," (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")
            (Term.explicitBinder "(" [`p] [":" (Term.app `r [`a `b])] [] ")")]
           []
           ","
           («term_=_»
            (Term.typeAscription
             "("
             (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
             ":"
             [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
             ")")
            "="
            (Term.app `f [`b])))]
         []
         ")")
        (Term.explicitBinder "(" [`q] [":" (Term.app `Quot [`r])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj
          (Term.app `lift [(Term.app `Quot.indep [`f]) (Term.app `Quot.indep_coherent [`f `h]) `q])
          "."
          (fieldIdx "1"))
         "="
         `q)))
      (Command.declValSimple
       ":="
       (Term.app
        `Quot.ind
        [(Term.fun
          "fun"
          (Term.basicFun
           [`a]
           [(Term.typeSpec ":" `α)]
           "=>"
           (Term.app `Eq.refl [(Term.proj (Term.app `Quot.indep [`f `a]) "." (fieldIdx "1"))])))
         `q])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quot.ind
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a]
          [(Term.typeSpec ":" `α)]
          "=>"
          (Term.app `Eq.refl [(Term.proj (Term.app `Quot.indep [`f `a]) "." (fieldIdx "1"))])))
        `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        [(Term.typeSpec ":" `α)]
        "=>"
        (Term.app `Eq.refl [(Term.proj (Term.app `Quot.indep [`f `a]) "." (fieldIdx "1"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.refl [(Term.proj (Term.app `Quot.indep [`f `a]) "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Quot.indep [`f `a]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Quot.indep [`f `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.indep
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Quot.indep [`f `a]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`a]
       [(Term.typeSpec ":" `α)]
       "=>"
       (Term.app
        `Eq.refl
        [(Term.proj (Term.paren "(" (Term.app `Quot.indep [`f `a]) ")") "." (fieldIdx "1"))])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.ind
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj
        (Term.app `lift [(Term.app `Quot.indep [`f]) (Term.app `Quot.indep_coherent [`f `h]) `q])
        "."
        (fieldIdx "1"))
       "="
       `q)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj
       (Term.app `lift [(Term.app `Quot.indep [`f]) (Term.app `Quot.indep_coherent [`f `h]) `q])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `lift [(Term.app `Quot.indep [`f]) (Term.app `Quot.indep_coherent [`f `h]) `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Quot.indep_coherent [`f `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.indep_coherent
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Quot.indep_coherent [`f `h])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Quot.indep [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.indep
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Quot.indep [`f]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `lift
      [(Term.paren "(" (Term.app `Quot.indep [`f]) ")")
       (Term.paren "(" (Term.app `Quot.indep_coherent [`f `h]) ")")
       `q])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Quot [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")
        (Term.explicitBinder "(" [`p] [":" (Term.app `r [`a `b])] [] ")")]
       []
       ","
       («term_=_»
        (Term.typeAscription
         "("
         (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
         ":"
         [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
         ")")
        "="
        (Term.app `f [`b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
        ":"
        [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
        ")")
       "="
       (Term.app `f [`b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
       ":"
       [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Quot.Init.Data.Quot.term⟦_⟧._@.Init.Data.Quot._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    lift_indep_pr1
    ( f : ∀ a , β ⟦ a ⟧ )
        ( h : ∀ ( a b : α ) ( p : r a b ) , ( Eq.ndrec f a sound p : β ⟦ b ⟧ ) = f b )
        ( q : Quot r )
      : lift Quot.indep f Quot.indep_coherent f h q . 1 = q
    := Quot.ind fun a : α => Eq.refl Quot.indep f a . 1 q
#align quot.lift_indep_pr1 Quot.lift_indep_pr1

#print Quot.rec /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible []))
         ","
         (Term.attrInstance (Term.attrKind []) (Attr.simple `elab_as_elim []))]
        "]")]
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `rec [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.forall "∀" [`a] [] "," (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")
            (Term.explicitBinder "(" [`p] [":" (Term.app `r [`a `b])] [] ")")]
           []
           ","
           («term_=_»
            (Term.typeAscription
             "("
             (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
             ":"
             [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
             ")")
            "="
            (Term.app `f [`b])))]
         []
         ")")
        (Term.explicitBinder "(" [`q] [":" (Term.app `Quot [`r])] [] ")")]
       [(Term.typeSpec ":" (Term.app `β [`q]))])
      (Command.declValSimple
       ":="
       (Term.app
        `Eq.recOn
        [(Term.app `Quot.lift_indep_pr1 [`f `h `q])
         (Term.proj
          (Term.app `lift [(Term.app `Quot.indep [`f]) (Term.app `Quot.indep_coherent [`f `h]) `q])
          "."
          (fieldIdx "2"))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Eq.recOn
       [(Term.app `Quot.lift_indep_pr1 [`f `h `q])
        (Term.proj
         (Term.app `lift [(Term.app `Quot.indep [`f]) (Term.app `Quot.indep_coherent [`f `h]) `q])
         "."
         (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `lift [(Term.app `Quot.indep [`f]) (Term.app `Quot.indep_coherent [`f `h]) `q])
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `lift [(Term.app `Quot.indep [`f]) (Term.app `Quot.indep_coherent [`f `h]) `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Quot.indep_coherent [`f `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.indep_coherent
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Quot.indep_coherent [`f `h])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Quot.indep [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.indep
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Quot.indep [`f]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `lift
      [(Term.paren "(" (Term.app `Quot.indep [`f]) ")")
       (Term.paren "(" (Term.app `Quot.indep_coherent [`f `h]) ")")
       `q])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Quot.lift_indep_pr1 [`f `h `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.lift_indep_pr1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Quot.lift_indep_pr1 [`f `h `q])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `β [`q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Quot [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")
        (Term.explicitBinder "(" [`p] [":" (Term.app `r [`a `b])] [] ")")]
       []
       ","
       («term_=_»
        (Term.typeAscription
         "("
         (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
         ":"
         [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
         ")")
        "="
        (Term.app `f [`b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
        ":"
        [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
        ")")
       "="
       (Term.app `f [`b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
       ":"
       [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Quot.Init.Data.Quot.term⟦_⟧._@.Init.Data.Quot._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ reducible , elab_as_elim ] protected
  def
    rec
    ( f : ∀ a , β ⟦ a ⟧ )
        ( h : ∀ ( a b : α ) ( p : r a b ) , ( Eq.ndrec f a sound p : β ⟦ b ⟧ ) = f b )
        ( q : Quot r )
      : β q
    := Eq.recOn Quot.lift_indep_pr1 f h q lift Quot.indep f Quot.indep_coherent f h q . 2
#align quot.rec Quot.rec
-/

#print Quot.recOn /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible []))
         ","
         (Term.attrInstance (Term.attrKind []) (Attr.simple `elab_as_elim []))]
        "]")]
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `recOn [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`q] [":" (Term.app `Quot [`r])] [] ")")
        (Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.forall "∀" [`a] [] "," (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")
            (Term.explicitBinder "(" [`p] [":" (Term.app `r [`a `b])] [] ")")]
           []
           ","
           («term_=_»
            (Term.typeAscription
             "("
             (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
             ":"
             [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
             ")")
            "="
            (Term.app `f [`b])))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `β [`q]))])
      (Command.declValSimple ":=" (Term.app `Quot.rec [`f `h `q]) [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Quot.rec [`f `h `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.rec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `β [`q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")
        (Term.explicitBinder "(" [`p] [":" (Term.app `r [`a `b])] [] ")")]
       []
       ","
       («term_=_»
        (Term.typeAscription
         "("
         (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
         ":"
         [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
         ")")
        "="
        (Term.app `f [`b])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
        ":"
        [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
        ")")
       "="
       (Term.app `f [`b]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
       ":"
       [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Quot.Init.Data.Quot.term⟦_⟧._@.Init.Data.Quot._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ reducible , elab_as_elim ] protected
  def
    recOn
    ( q : Quot r )
        ( f : ∀ a , β ⟦ a ⟧ )
        ( h : ∀ ( a b : α ) ( p : r a b ) , ( Eq.ndrec f a sound p : β ⟦ b ⟧ ) = f b )
      : β q
    := Quot.rec f h q
#align quot.rec_on Quot.recOn
-/

#print Quot.recOnSubsingleton /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible []))
         ","
         (Term.attrInstance (Term.attrKind []) (Attr.simple `elab_as_elim []))]
        "]")]
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `recOnSubsingleton [])
      (Command.optDeclSig
       [(Term.instBinder
         "["
         [`h ":"]
         (Term.forall
          "∀"
          [`a]
          []
          ","
          (Term.app `Subsingleton [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")])]))
         "]")
        (Term.explicitBinder "(" [`q] [":" (Term.app `Quot [`r])] [] ")")
        (Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.forall "∀" [`a] [] "," (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")]))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `β [`q]))])
      (Command.declValSimple
       ":="
       (Term.app
        `Quot.rec
        [`f
         (Term.fun
          "fun"
          (Term.basicFun
           [`a `b `h]
           []
           "=>"
           (Term.app `Subsingleton.elim [(Term.hole "_") (Term.app `f [`b])])))
         `q])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quot.rec
       [`f
        (Term.fun
         "fun"
         (Term.basicFun
          [`a `b `h]
          []
          "=>"
          (Term.app `Subsingleton.elim [(Term.hole "_") (Term.app `f [`b])])))
        `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `b `h]
        []
        "=>"
        (Term.app `Subsingleton.elim [(Term.hole "_") (Term.app `f [`b])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subsingleton.elim [(Term.hole "_") (Term.app `f [`b])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`b]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subsingleton.elim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`a `b `h]
       []
       "=>"
       (Term.app `Subsingleton.elim [(Term.hole "_") (Term.paren "(" (Term.app `f [`b]) ")")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.rec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `β [`q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall "∀" [`a] [] "," (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Quot.Init.Data.Quot.term⟦_⟧._@.Init.Data.Quot._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ reducible , elab_as_elim ] protected
  def
    recOnSubsingleton
    [ h : ∀ a , Subsingleton β ⟦ a ⟧ ] ( q : Quot r ) ( f : ∀ a , β ⟦ a ⟧ ) : β q
    := Quot.rec f fun a b h => Subsingleton.elim _ f b q
#align quot.rec_on_subsingleton Quot.recOnSubsingleton
-/

#print Quot.hrecOn /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `reducible []))
         ","
         (Term.attrInstance (Term.attrKind []) (Attr.simple `elab_as_elim []))]
        "]")]
      [(Command.protected "protected")]
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `hrecOn [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`q] [":" (Term.app `Quot [`r])] [] ")")
        (Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.forall "∀" [`a] [] "," (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `a "⟧")]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`c]
         [":"
          (Term.forall
           "∀"
           [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")
            (Term.explicitBinder "(" [`p] [":" (Term.app `r [`a `b])] [] ")")]
           []
           ","
           (Term.app `HEq [(Term.app `f [`a]) (Term.app `f [`b])]))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `β [`q]))])
      (Command.declValSimple
       ":="
       (Term.app
        `Quot.recOn
        [`q
         `f
         (Term.fun
          "fun"
          (Term.basicFun
           [`a `b `p]
           []
           "=>"
           (Term.app
            `eq_of_heq
            [(calc
              "calc"
              (calcStep
               (Term.app
                `HEq
                [(Term.typeAscription
                  "("
                  (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
                  ":"
                  [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
                  ")")
                 (Term.app `f [`a])])
               ":="
               (Term.app `eq_rec_heq [(Term.app `sound [`p]) (Term.app `f [`a])]))
              [(calcStep
                (Term.app `HEq [(Term.hole "_") (Term.app `f [`b])])
                ":="
                (Term.app `c [`a `b `p]))])])))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quot.recOn
       [`q
        `f
        (Term.fun
         "fun"
         (Term.basicFun
          [`a `b `p]
          []
          "=>"
          (Term.app
           `eq_of_heq
           [(calc
             "calc"
             (calcStep
              (Term.app
               `HEq
               [(Term.typeAscription
                 "("
                 (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
                 ":"
                 [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
                 ")")
                (Term.app `f [`a])])
              ":="
              (Term.app `eq_rec_heq [(Term.app `sound [`p]) (Term.app `f [`a])]))
             [(calcStep
               (Term.app `HEq [(Term.hole "_") (Term.app `f [`b])])
               ":="
               (Term.app `c [`a `b `p]))])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `b `p]
        []
        "=>"
        (Term.app
         `eq_of_heq
         [(calc
           "calc"
           (calcStep
            (Term.app
             `HEq
             [(Term.typeAscription
               "("
               (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
               ":"
               [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
               ")")
              (Term.app `f [`a])])
            ":="
            (Term.app `eq_rec_heq [(Term.app `sound [`p]) (Term.app `f [`a])]))
           [(calcStep
             (Term.app `HEq [(Term.hole "_") (Term.app `f [`b])])
             ":="
             (Term.app `c [`a `b `p]))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eq_of_heq
       [(calc
         "calc"
         (calcStep
          (Term.app
           `HEq
           [(Term.typeAscription
             "("
             (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
             ":"
             [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
             ")")
            (Term.app `f [`a])])
          ":="
          (Term.app `eq_rec_heq [(Term.app `sound [`p]) (Term.app `f [`a])]))
         [(calcStep
           (Term.app `HEq [(Term.hole "_") (Term.app `f [`b])])
           ":="
           (Term.app `c [`a `b `p]))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        (Term.app
         `HEq
         [(Term.typeAscription
           "("
           (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
           ":"
           [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
           ")")
          (Term.app `f [`a])])
        ":="
        (Term.app `eq_rec_heq [(Term.app `sound [`p]) (Term.app `f [`a])]))
       [(calcStep
         (Term.app `HEq [(Term.hole "_") (Term.app `f [`b])])
         ":="
         (Term.app `c [`a `b `p]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `c [`a `b `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HEq [(Term.hole "_") (Term.app `f [`b])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`b]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HEq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `eq_rec_heq [(Term.app `sound [`p]) (Term.app `f [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`a]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `sound [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sound
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `sound [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_rec_heq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `HEq
       [(Term.typeAscription
         "("
         (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
         ":"
         [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
         ")")
        (Term.app `f [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`a]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (Term.app `Eq.ndrec [(Term.app `f [`a]) (Term.app `sound [`p])])
       ":"
       [(Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `β [(Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quot.Init.Data.Quot.«term⟦_⟧» "⟦" `b "⟧")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quot.Init.Data.Quot.«term⟦_⟧»', expected 'Quot.Init.Data.Quot.term⟦_⟧._@.Init.Data.Quot._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ reducible , elab_as_elim ] protected
  def
    hrecOn
    ( q : Quot r ) ( f : ∀ a , β ⟦ a ⟧ ) ( c : ∀ ( a b : α ) ( p : r a b ) , HEq f a f b ) : β q
    :=
      Quot.recOn
        q
          f
          fun
            a b p
              =>
              eq_of_heq
                calc
                  HEq ( Eq.ndrec f a sound p : β ⟦ b ⟧ ) f a := eq_rec_heq sound p f a
                  HEq _ f b := c a b p
#align quot.hrec_on Quot.hrecOn
-/

end

end Quot

#print Quotient /-
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r
#align quotient Quotient
-/

namespace Quotient

#print Quotient.mk'' /-
protected def mk'' {α : Sort u} [s : Setoid α] (a : α) : Quotient s :=
  Quot.mk Setoid.r a
#align quotient.mk Quotient.mk''
-/

-- mathport name: «expr⟦ ⟧»
notation:arg "⟦" a "⟧" => Quotient.mk'' a

#print Quotient.sound /-
theorem sound {α : Sort u} [s : Setoid α] {a b : α} : a ≈ b → ⟦a⟧ = ⟦b⟧ :=
  Quot.sound
#align quotient.sound Quotient.sound
-/

#print Quotient.lift /-
@[reducible, elab_as_elim]
protected def lift {α : Sort u} {β : Sort v} [s : Setoid α] (f : α → β) :
    (∀ a b, a ≈ b → f a = f b) → Quotient s → β :=
  Quot.lift f
#align quotient.lift Quotient.lift
-/

#print Quotient.ind /-
@[elab_as_elim]
protected theorem ind {α : Sort u} [s : Setoid α] {β : Quotient s → Prop} :
    (∀ a, β ⟦a⟧) → ∀ q, β q :=
  Quot.ind
#align quotient.ind Quotient.ind
-/

#print Quotient.liftOn /-
@[reducible, elab_as_elim]
protected def liftOn {α : Sort u} {β : Sort v} [s : Setoid α] (q : Quotient s) (f : α → β)
    (c : ∀ a b, a ≈ b → f a = f b) : β :=
  Quot.liftOn q f c
#align quotient.lift_on Quotient.liftOn
-/

@[elab_as_elim]
protected theorem induction_on {α : Sort u} [s : Setoid α] {β : Quotient s → Prop} (q : Quotient s)
    (h : ∀ a, β ⟦a⟧) : β q :=
  Quot.induction_on q h
#align quotient.induction_on Quotient.induction_on

#print Quotient.exists_rep /-
theorem exists_rep {α : Sort u} [s : Setoid α] (q : Quotient s) : ∃ a : α, ⟦a⟧ = q :=
  Quot.exists_rep q
#align quotient.exists_rep Quotient.exists_rep
-/

section

variable {α : Sort u}

variable [s : Setoid α]

variable {β : Quotient s → Sort v}

#print Quotient.rec /-
protected def rec (f : ∀ a, β ⟦a⟧)
    (h : ∀ (a b : α) (p : a ≈ b), (Eq.ndrec (f a) (Quotient.sound p) : β ⟦b⟧) = f b)
    (q : Quotient s) : β q :=
  Quot.rec f h q
#align quotient.rec Quotient.rec
-/

#print Quotient.recOn /-
@[reducible, elab_as_elim]
protected def recOn (q : Quotient s) (f : ∀ a, β ⟦a⟧)
    (h : ∀ (a b : α) (p : a ≈ b), (Eq.ndrec (f a) (Quotient.sound p) : β ⟦b⟧) = f b) : β q :=
  Quot.recOn q f h
#align quotient.rec_on Quotient.recOn
-/

#print Quotient.recOnSubsingleton /-
@[reducible, elab_as_elim]
protected def recOnSubsingleton [h : ∀ a, Subsingleton (β ⟦a⟧)] (q : Quotient s) (f : ∀ a, β ⟦a⟧) :
    β q :=
  @Quot.recOnSubsingleton _ _ _ h q f
#align quotient.rec_on_subsingleton Quotient.recOnSubsingleton
-/

#print Quotient.hrecOn /-
@[reducible, elab_as_elim]
protected def hrecOn (q : Quotient s) (f : ∀ a, β ⟦a⟧)
    (c : ∀ (a b : α) (p : a ≈ b), HEq (f a) (f b)) : β q :=
  Quot.hrecOn q f c
#align quotient.hrec_on Quotient.hrecOn
-/

end

section

universe u_a u_b u_c

variable {α : Sort u_a} {β : Sort u_b} {φ : Sort u_c}

variable [s₁ : Setoid α] [s₂ : Setoid β]

include s₁ s₂

#print Quotient.lift₂ /-
@[reducible, elab_as_elim]
protected def lift₂ (f : α → β → φ) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) : φ :=
  Quotient.lift
    (fun a₁ : α => Quotient.lift (f a₁) (fun a b : β => c a₁ a a₁ b (Setoid.refl a₁)) q₂)
    (fun (a b : α) (h : a ≈ b) =>
      @Quotient.ind β s₂
        (fun a_1 : Quotient s₂ =>
          Quotient.lift (f a) (fun a_1 b : β => c a a_1 a b (Setoid.refl a)) a_1 =
            Quotient.lift (f b) (fun a b_1 : β => c b a b b_1 (Setoid.refl b)) a_1)
        (fun a' : β => c a a' b a' h (Setoid.refl a')) q₂)
    q₁
#align quotient.lift₂ Quotient.lift₂
-/

#print Quotient.liftOn₂ /-
@[reducible, elab_as_elim]
protected def liftOn₂ (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α → β → φ)
    (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : φ :=
  Quotient.lift₂ f c q₁ q₂
#align quotient.lift_on₂ Quotient.liftOn₂
-/

#print Quotient.ind₂ /-
@[elab_as_elim]
protected theorem ind₂ {φ : Quotient s₁ → Quotient s₂ → Prop} (h : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) : φ q₁ q₂ :=
  Quotient.ind (fun a₁ => Quotient.ind (fun a₂ => h a₁ a₂) q₂) q₁
#align quotient.ind₂ Quotient.ind₂
-/

@[elab_as_elim]
protected theorem induction_on₂ {φ : Quotient s₁ → Quotient s₂ → Prop} (q₁ : Quotient s₁)
    (q₂ : Quotient s₂) (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  Quotient.ind (fun a₁ => Quotient.ind (fun a₂ => h a₁ a₂) q₂) q₁
#align quotient.induction_on₂ Quotient.induction_on₂

@[elab_as_elim]
protected theorem induction_on₃ [s₃ : Setoid φ] {δ : Quotient s₁ → Quotient s₂ → Quotient s₃ → Prop}
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) (q₃ : Quotient s₃) (h : ∀ a b c, δ ⟦a⟧ ⟦b⟧ ⟦c⟧) :
    δ q₁ q₂ q₃ :=
  Quotient.ind (fun a₁ => Quotient.ind (fun a₂ => Quotient.ind (fun a₃ => h a₁ a₂ a₃) q₃) q₂) q₁
#align quotient.induction_on₃ Quotient.induction_on₃

end

section Exact

variable {α : Sort u}

variable [s : Setoid α]

include s

private def rel (q₁ q₂ : Quotient s) : Prop :=
  Quotient.liftOn₂ q₁ q₂ (fun a₁ a₂ => a₁ ≈ a₂) fun a₁ a₂ b₁ b₂ a₁b₁ a₂b₂ =>
    propext
      (Iff.intro (fun a₁a₂ => Setoid.trans (Setoid.symm a₁b₁) (Setoid.trans a₁a₂ a₂b₂)) fun b₁b₂ =>
        Setoid.trans a₁b₁ (Setoid.trans b₁b₂ (Setoid.symm a₂b₂)))
#align quotient.rel quotient.rel

-- mathport name: «expr ~ »
local infixl:50 " ~ " => Rel

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.private "private")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `rel.refl [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`q]
         [(Term.typeSpec ":" (Term.app `Quotient [`s]))]
         ","
         (Quotient.Init.Data.Quot.«term_~_» `q " ~ " `q))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`q]
         []
         "=>"
         (Term.app
          `Quot.induction_on
          [`q (Term.fun "fun" (Term.basicFun [`a] [] "=>" (Term.app `Setoid.refl [`a])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`q]
        []
        "=>"
        (Term.app
         `Quot.induction_on
         [`q (Term.fun "fun" (Term.basicFun [`a] [] "=>" (Term.app `Setoid.refl [`a])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quot.induction_on
       [`q (Term.fun "fun" (Term.basicFun [`a] [] "=>" (Term.app `Setoid.refl [`a])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" (Term.app `Setoid.refl [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Setoid.refl [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Setoid.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quot.induction_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`q]
       [(Term.typeSpec ":" (Term.app `Quotient [`s]))]
       ","
       (Quotient.Init.Data.Quot.«term_~_» `q " ~ " `q))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quotient.Init.Data.Quot.«term_~_» `q " ~ " `q)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quotient.Init.Data.Quot.«term_~_»', expected 'Quotient.Init.Data.Quot.term_~_._@.Init.Data.Quot._hyg.1177'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
private
  theorem rel.refl : ∀ q : Quotient s , q ~ q := fun q => Quot.induction_on q fun a => Setoid.refl a
#align quotient.rel.refl quotient.rel.refl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.private "private")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_imp_rel [])
      (Command.declSig
       [(Term.implicitBinder "{" [`q₁ `q₂] [":" (Term.app `Quotient [`s])] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow («term_=_» `q₁ "=" `q₂) "→" (Quotient.Init.Data.Quot.«term_~_» `q₁ " ~ " `q₂))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun [`h] [] "=>" (Term.app `Eq.recOn [`h (Term.app `Rel.refl [`q₁])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`h] [] "=>" (Term.app `Eq.recOn [`h (Term.app `Rel.refl [`q₁])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.recOn [`h (Term.app `Rel.refl [`q₁])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Rel.refl [`q₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Rel.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Rel.refl [`q₁]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow («term_=_» `q₁ "=" `q₂) "→" (Quotient.Init.Data.Quot.«term_~_» `q₁ " ~ " `q₂))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Quotient.Init.Data.Quot.«term_~_» `q₁ " ~ " `q₂)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Quotient.Init.Data.Quot.«term_~_»', expected 'Quotient.Init.Data.Quot.term_~_._@.Init.Data.Quot._hyg.1177'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
private
  theorem eq_imp_rel { q₁ q₂ : Quotient s } : q₁ = q₂ → q₁ ~ q₂ := fun h => Eq.recOn h Rel.refl q₁
#align quotient.eq_imp_rel quotient.eq_imp_rel

#print Quotient.exact /-
theorem exact {a b : α} : ⟦a⟧ = ⟦b⟧ → a ≈ b := fun h => eq_imp_rel h
#align quotient.exact Quotient.exact
-/

end Exact

section

universe u_a u_b u_c

variable {α : Sort u_a} {β : Sort u_b}

variable [s₁ : Setoid α] [s₂ : Setoid β]

include s₁ s₂

#print Quotient.recOnSubsingleton₂ /-
@[reducible, elab_as_elim]
protected def recOnSubsingleton₂ {φ : Quotient s₁ → Quotient s₂ → Sort u_c}
    [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)] (q₁ : Quotient s₁) (q₂ : Quotient s₂)
    (f : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  @Quotient.recOnSubsingleton _ s₁ (fun q => φ q q₂) (fun a => Quotient.ind (fun b => h a b) q₂) q₁
    fun a => Quotient.recOnSubsingleton q₂ fun b => f a b
#align quotient.rec_on_subsingleton₂ Quotient.recOnSubsingleton₂
-/

end

end Quotient

section

variable {α : Type u}

variable (r : α → α → Prop)

#print EqvGen /-
inductive EqvGen : α → α → Prop
  | Rel : ∀ x y, r x y → EqvGen x y
  | refl : ∀ x, EqvGen x x
  | symm : ∀ x y, EqvGen x y → EqvGen y x
  | trans : ∀ x y z, EqvGen x y → EqvGen y z → EqvGen x z
#align eqv_gen EqvGen
-/

#print EqvGen.is_equivalence /-
theorem EqvGen.is_equivalence : Equivalence (@EqvGen α r) :=
  Equivalence.mk _ EqvGen.refl EqvGen.symm EqvGen.trans
#align eqv_gen.is_equivalence EqvGen.is_equivalence
-/

#print EqvGen.Setoid /-
def EqvGen.Setoid : Setoid α :=
  Setoid.mk _ (EqvGen.is_equivalence r)
#align eqv_gen.setoid EqvGen.Setoid
-/

#print Quot.exact /-
theorem Quot.exact {a b : α} (H : Quot.mk r a = Quot.mk r b) : EqvGen r a b :=
  @Quotient.exact _ (EqvGen.Setoid r) a b
    (@congr_arg _ _ _ _
      (Quot.lift (@Quotient.mk'' _ (EqvGen.Setoid r)) fun x y h => Quot.sound (EqvGen.rel x y h)) H)
#align quot.exact Quot.exact
-/

#print Quot.EqvGen_sound /-
theorem Quot.EqvGen_sound {r : α → α → Prop} {a b : α} (H : EqvGen r a b) :
    Quot.mk r a = Quot.mk r b :=
  EqvGen.rec_on H (fun x y h => Quot.sound h) (fun x => rfl) (fun x y _ IH => Eq.symm IH)
    fun x y z _ _ IH₁ IH₂ => Eq.trans IH₁ IH₂
#align quot.eqv_gen_sound Quot.EqvGen_sound
-/

end

open Decidable

instance {α : Sort u} {s : Setoid α} [d : ∀ a b : α, Decidable (a ≈ b)] :
    DecidableEq (Quotient s) := fun q₁ q₂ : Quotient s =>
  Quotient.recOnSubsingleton₂ q₁ q₂ fun a₁ a₂ =>
    match d a₁ a₂ with
    | is_true h₁ => isTrue (Quotient.sound h₁)
    | is_false h₂ => isFalse fun h => absurd (Quotient.exact h) h₂

