/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Extensional equality for functions, and a proof of function extensionality from quotients.

! This file was ported from Lean 3 source module init.funext
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Quot
import Leanbin.Init.Logic

open Quotient

universe u v

variable {α : Sort u} {β : α → Sort v}

namespace Function

/-- The relation stating that two functions are pointwise equal. -/
protected def Equiv (f₁ f₂ : ∀ x : α, β x) : Prop :=
  ∀ x, f₁ x = f₂ x
#align function.equiv Function.Equiv

-- mathport name: «expr ~ »
local infixl:50 " ~ " => Function.Equiv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Equiv.refl [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Term.forall "∀" [`x] [(Term.typeSpec ":" `α)] "," (Term.app `β [`x]))]
         []
         ")")]
       (Term.typeSpec ":" (Function.Init.Funext.«term_~_» `f " ~ " `f)))
      (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [`x] [] "=>" `rfl)) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Function.Init.Funext.«term_~_» `f " ~ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Function.Init.Funext.«term_~_»', expected 'Function.Init.Funext.term_~_._@.Init.Funext._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected theorem Equiv.refl ( f : ∀ x : α , β x ) : f ~ f := fun x => rfl
#align function.equiv.refl Function.Equiv.refl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Equiv.symm [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f₁ `f₂]
         [":" (Term.forall "∀" [`x] [(Term.typeSpec ":" `α)] "," (Term.app `β [`x]))]
         "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Function.Init.Funext.«term_~_» `f₁ " ~ " `f₂)
         "→"
         (Function.Init.Funext.«term_~_» `f₂ " ~ " `f₁))))
      (Command.declValSimple
       ":="
       (Term.fun "fun" (Term.basicFun [`h `x] [] "=>" (Term.app `Eq.symm [(Term.app `h [`x])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h `x] [] "=>" (Term.app `Eq.symm [(Term.app `h [`x])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.symm [(Term.app `h [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Function.Init.Funext.«term_~_» `f₁ " ~ " `f₂)
       "→"
       (Function.Init.Funext.«term_~_» `f₂ " ~ " `f₁))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Function.Init.Funext.«term_~_» `f₂ " ~ " `f₁)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Function.Init.Funext.«term_~_»', expected 'Function.Init.Funext.term_~_._@.Init.Funext._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected theorem Equiv.symm { f₁ f₂ : ∀ x : α , β x } : f₁ ~ f₂ → f₂ ~ f₁ := fun h x => Eq.symm h x
#align function.equiv.symm Function.Equiv.symm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Equiv.trans [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f₁ `f₂ `f₃]
         [":" (Term.forall "∀" [`x] [(Term.typeSpec ":" `α)] "," (Term.app `β [`x]))]
         "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Function.Init.Funext.«term_~_» `f₁ " ~ " `f₂)
         "→"
         (Term.arrow
          (Function.Init.Funext.«term_~_» `f₂ " ~ " `f₃)
          "→"
          (Function.Init.Funext.«term_~_» `f₁ " ~ " `f₃)))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`h₁ `h₂ `x]
         []
         "=>"
         (Term.app `Eq.trans [(Term.app `h₁ [`x]) (Term.app `h₂ [`x])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h₁ `h₂ `x]
        []
        "=>"
        (Term.app `Eq.trans [(Term.app `h₁ [`x]) (Term.app `h₂ [`x])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.trans [(Term.app `h₁ [`x]) (Term.app `h₂ [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h₂ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h₂ [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `h₁ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h₁ [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Function.Init.Funext.«term_~_» `f₁ " ~ " `f₂)
       "→"
       (Term.arrow
        (Function.Init.Funext.«term_~_» `f₂ " ~ " `f₃)
        "→"
        (Function.Init.Funext.«term_~_» `f₁ " ~ " `f₃)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Function.Init.Funext.«term_~_» `f₂ " ~ " `f₃)
       "→"
       (Function.Init.Funext.«term_~_» `f₁ " ~ " `f₃))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Function.Init.Funext.«term_~_» `f₁ " ~ " `f₃)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Function.Init.Funext.«term_~_»', expected 'Function.Init.Funext.term_~_._@.Init.Funext._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    Equiv.trans
    { f₁ f₂ f₃ : ∀ x : α , β x } : f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃
    := fun h₁ h₂ x => Eq.trans h₁ x h₂ x
#align function.equiv.trans Function.Equiv.trans

protected theorem Equiv.is_equivalence (α : Sort u) (β : α → Sort v) :
    Equivalence (@Function.Equiv α β) :=
  Equivalence.mk (@Function.Equiv α β) (@Equiv.refl α β) (@Equiv.symm α β) (@Equiv.trans α β)
#align function.equiv.is_equivalence Function.Equiv.is_equivalence

/-- The setoid generated by pointwise equality. -/
@[local instance]
def funSetoid (α : Sort u) (β : α → Sort v) : Setoid (∀ x : α, β x) :=
  Setoid.mk (@Function.Equiv α β) (Function.Equiv.is_equivalence α β)
#align function.fun_setoid Function.funSetoid

/-- The quotient of the function type by pointwise equality. -/
def Extfun (α : Sort u) (β : α → Sort v) : Sort imax u v :=
  Quotient (funSetoid α β)
#align function.extfun Function.Extfun

/-- The map from functions into the qquotient by pointwise equality. -/
def funToExtfun (f : ∀ x : α, β x) : Extfun α β :=
  ⟦f⟧
#align function.fun_to_extfun Function.funToExtfun

/-- From an element of `extfun` we can retrieve an actual function. -/
def extfunApp (f : Extfun α β) : ∀ x : α, β x := fun x =>
  Quot.liftOn f (fun f : ∀ x : α, β x => f x) fun f₁ f₂ h => h x
#align function.extfun_app Function.extfunApp

end Function

open Function

attribute [local instance] fun_setoid

#print funext /-
/-- Function extensionality, proven using quotients. -/
theorem funext {f₁ f₂ : ∀ x : α, β x} (h : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
  show extfunApp ⟦f₁⟧ = extfunApp ⟦f₂⟧ from congr_arg extfunApp (sound h)
#align funext funext
-/

attribute [intro!] funext

-- mathport name: «expr ~ »
local infixl:50 " ~ " => Function.Equiv

instance Pi.subsingleton [∀ a, Subsingleton (β a)] : Subsingleton (∀ a, β a) :=
  ⟨fun f₁ f₂ => funext fun a => Subsingleton.elim (f₁ a) (f₂ a)⟩
#align pi.subsingleton Pi.subsingleton

