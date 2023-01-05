/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.algebra.classes
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Logic
import Leanbin.Init.Data.Ordering.Basic

universe u v

/-!
# Unbundled algebra classes

These classes and the `@[algebra]` attribute are part of an incomplete refactor described
[here on the github Wiki](https://github.com/leanprover/lean/wiki/Refactoring-structures#encoding-the-algebraic-hierarchy-1).

By themselves, these classes are not good replacements for the `monoid` / `group` etc structures
provided by mathlib, as they are not discoverable by `simp` unlike the current lemmas due to there
being little to index on. The Wiki page linked above describes an algebraic normalizer, but it is not
implemented.
-/


#print IsSymmOp /-
class IsSymmOp (α : Type u) (β : outParam (Type v)) (op : α → α → β) : Prop where
  symm_op : ∀ a b, op a b = op b a
#align is_symm_op IsSymmOp
-/

#print IsCommutative /-
class IsCommutative (α : Type u) (op : α → α → α) : Prop where
  comm : ∀ a b, op a b = op b a
#align is_commutative IsCommutative
-/

instance (priority := 100) is_symm_op_of_is_commutative (α : Type u) (op : α → α → α)
    [IsCommutative α op] : IsSymmOp α α op where symm_op := IsCommutative.comm
#align is_symm_op_of_is_commutative is_symm_op_of_is_commutative

#print IsAssociative /-
class IsAssociative (α : Type u) (op : α → α → α) : Prop where
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
#align is_associative IsAssociative
-/

#print IsLeftId /-
class IsLeftId (α : Type u) (op : α → α → α) (o : outParam α) : Prop where
  left_id : ∀ a, op o a = a
#align is_left_id IsLeftId
-/

#print IsRightId /-
class IsRightId (α : Type u) (op : α → α → α) (o : outParam α) : Prop where
  right_id : ∀ a, op a o = a
#align is_right_id IsRightId
-/

class IsLeftNull (α : Type u) (op : α → α → α) (o : outParam α) : Prop where
  left_null : ∀ a, op o a = o
#align is_left_null IsLeftNull

class IsRightNull (α : Type u) (op : α → α → α) (o : outParam α) : Prop where
  right_null : ∀ a, op a o = o
#align is_right_null IsRightNull

#print IsLeftCancel /-
class IsLeftCancel (α : Type u) (op : α → α → α) : Prop where
  left_cancel : ∀ a b c, op a b = op a c → b = c
#align is_left_cancel IsLeftCancel
-/

#print IsRightCancel /-
class IsRightCancel (α : Type u) (op : α → α → α) : Prop where
  right_cancel : ∀ a b c, op a b = op c b → a = c
#align is_right_cancel IsRightCancel
-/

#print IsIdempotent /-
class IsIdempotent (α : Type u) (op : α → α → α) : Prop where
  idempotent : ∀ a, op a a = a
#align is_idempotent IsIdempotent
-/

class IsLeftDistrib (α : Type u) (op₁ : α → α → α) (op₂ : outParam <| α → α → α) : Prop where
  left_distrib : ∀ a b c, op₁ a (op₂ b c) = op₂ (op₁ a b) (op₁ a c)
#align is_left_distrib IsLeftDistrib

class IsRightDistrib (α : Type u) (op₁ : α → α → α) (op₂ : outParam <| α → α → α) : Prop where
  right_distrib : ∀ a b c, op₁ (op₂ a b) c = op₂ (op₁ a c) (op₁ b c)
#align is_right_distrib IsRightDistrib

class IsLeftInv (α : Type u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α) :
  Prop where
  left_inv : ∀ a, op (inv a) a = o
#align is_left_inv IsLeftInv

class IsRightInv (α : Type u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α) :
  Prop where
  right_inv : ∀ a, op a (inv a) = o
#align is_right_inv IsRightInv

class IsCondLeftInv (α : Type u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α)
  (p : outParam <| α → Prop) : Prop where
  left_inv : ∀ a, p a → op (inv a) a = o
#align is_cond_left_inv IsCondLeftInv

class IsCondRightInv (α : Type u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α)
  (p : outParam <| α → Prop) : Prop where
  right_inv : ∀ a, p a → op a (inv a) = o
#align is_cond_right_inv IsCondRightInv

class IsDistinct (α : Type u) (a : α) (b : α) : Prop where
  distinct : a ≠ b
#align is_distinct IsDistinct

#print IsIrrefl /-
/-
-- The following type class doesn't seem very useful, a regular simp lemma should work for this.
class is_inv (α : Type u) (β : Type v) (f : α → β) (g : out β → α) : Prop :=
(inv : ∀ a, g (f a) = a)

-- The following one can also be handled using a regular simp lemma
class is_idempotent (α : Type u) (f : α → α) : Prop :=
(idempotent : ∀ a, f (f a) = f a)
-/
/-- `is_irrefl X r` means the binary relation `r` on `X` is irreflexive (that is, `r x x` never
holds). -/
class IsIrrefl (α : Type u) (r : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬r a a
#align is_irrefl IsIrrefl
-/

#print IsRefl /-
/-- `is_refl X r` means the binary relation `r` on `X` is reflexive. -/
class IsRefl (α : Type u) (r : α → α → Prop) : Prop where
  refl : ∀ a, r a a
#align is_refl IsRefl
-/

#print IsSymm /-
/-- `is_symm X r` means the binary relation `r` on `X` is symmetric. -/
class IsSymm (α : Type u) (r : α → α → Prop) : Prop where
  symm : ∀ a b, r a b → r b a
#align is_symm IsSymm
-/

/-- The opposite of a symmetric relation is symmetric. -/
instance (priority := 100) is_symm_op_of_is_symm (α : Type u) (r : α → α → Prop) [IsSymm α r] :
    IsSymmOp α Prop r where symm_op a b := propext <| Iff.intro (IsSymm.symm a b) (IsSymm.symm b a)
#align is_symm_op_of_is_symm is_symm_op_of_is_symm

#print IsAsymm /-
/-- `is_asymm X r` means that the binary relation `r` on `X` is asymmetric, that is,
`r a b → ¬ r b a`. -/
class IsAsymm (α : Type u) (r : α → α → Prop) : Prop where
  asymm : ∀ a b, r a b → ¬r b a
#align is_asymm IsAsymm
-/

#print IsAntisymm /-
/-- `is_antisymm X r` means the binary relation `r` on `X` is antisymmetric. -/
class IsAntisymm (α : Type u) (r : α → α → Prop) : Prop where
  antisymm : ∀ a b, r a b → r b a → a = b
#align is_antisymm IsAntisymm
-/

#print IsTrans /-
/-- `is_trans X r` means the binary relation `r` on `X` is transitive. -/
class IsTrans (α : Type u) (r : α → α → Prop) : Prop where
  trans : ∀ a b c, r a b → r b c → r a c
#align is_trans IsTrans
-/

#print IsTotal /-
/-- `is_total X r` means that the binary relation `r` on `X` is total, that is, that for any
`x y : X` we have `r x y` or `r y x`.-/
class IsTotal (α : Type u) (r : α → α → Prop) : Prop where
  Total : ∀ a b, r a b ∨ r b a
#align is_total IsTotal
-/

#print IsPreorder /-
/-- `is_preorder X r` means that the binary relation `r` on `X` is a pre-order, that is, reflexive
and transitive. -/
class IsPreorder (α : Type u) (r : α → α → Prop) extends IsRefl α r, IsTrans α r : Prop
#align is_preorder IsPreorder
-/

#print IsTotalPreorder /-
/-- `is_total_preorder X r` means that the binary relation `r` on `X` is total and a preorder. -/
class IsTotalPreorder (α : Type u) (r : α → α → Prop) extends IsTrans α r, IsTotal α r : Prop
#align is_total_preorder IsTotalPreorder
-/

/-- Every total pre-order is a pre-order. -/
instance is_total_preorder_is_preorder (α : Type u) (r : α → α → Prop) [s : IsTotalPreorder α r] :
    IsPreorder α r where
  trans := s.trans
  refl a := Or.elim (@IsTotal.total _ r _ a a) id id
#align is_total_preorder_is_preorder is_total_preorder_is_preorder

#print IsPartialOrder /-
/-- `is_partial_order X r` means that the binary relation `r` on `X` is a partial order, that is,
`is_preorder X r` and `is_antisymm X r`. -/
class IsPartialOrder (α : Type u) (r : α → α → Prop) extends IsPreorder α r, IsAntisymm α r : Prop
#align is_partial_order IsPartialOrder
-/

#print IsLinearOrder /-
/-- `is_linear_order X r` means that the binary relation `r` on `X` is a linear order, that is,
`is_partial_order X r` and `is_total X r`. -/
class IsLinearOrder (α : Type u) (r : α → α → Prop) extends IsPartialOrder α r, IsTotal α r : Prop
#align is_linear_order IsLinearOrder
-/

#print IsEquiv /-
/-- `is_equiv X r` means that the binary relation `r` on `X` is an equivalence relation, that
is, `is_preorder X r` and `is_symm X r`. -/
class IsEquiv (α : Type u) (r : α → α → Prop) extends IsPreorder α r, IsSymm α r : Prop
#align is_equiv IsEquiv
-/

/-- `is_per X r` means that the binary relation `r` on `X` is a partial equivalence relation, that
is, `is_symm X r` and `is_trans X r`. -/
class IsPer (α : Type u) (r : α → α → Prop) extends IsSymm α r, IsTrans α r : Prop
#align is_per IsPer

#print IsStrictOrder /-
/-- `is_strict_order X r` means that the binary relation `r` on `X` is a strict order, that is,
`is_irrefl X r` and `is_trans X r`. -/
class IsStrictOrder (α : Type u) (r : α → α → Prop) extends IsIrrefl α r, IsTrans α r : Prop
#align is_strict_order IsStrictOrder
-/

#print IsIncompTrans /-
/-- `is_incomp_trans X lt` means that for `lt` a binary relation on `X`, the incomparable relation
`λ a b, ¬ lt a b ∧ ¬ lt b a` is transitive. -/
class IsIncompTrans (α : Type u) (lt : α → α → Prop) : Prop where
  incomp_trans : ∀ a b c, ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a
#align is_incomp_trans IsIncompTrans
-/

#print IsStrictWeakOrder /-
/-- `is_strict_weak_order X lt` means that the binary relation `lt` on `X` is a strict weak order,
that is, `is_strict_order X lt` and `is_incomp_trans X lt`. -/
class IsStrictWeakOrder (α : Type u) (lt : α → α → Prop) extends IsStrictOrder α lt,
  IsIncompTrans α lt : Prop
#align is_strict_weak_order IsStrictWeakOrder
-/

#print IsTrichotomous /-
/-- `is_trichotomous X lt` means that the binary relation `lt` on `X` is trichotomous, that is,
either `lt a b` or `a = b` or `lt b a` for any `a` and `b`. -/
class IsTrichotomous (α : Type u) (lt : α → α → Prop) : Prop where
  trichotomous : ∀ a b, lt a b ∨ a = b ∨ lt b a
#align is_trichotomous IsTrichotomous
-/

#print IsStrictTotalOrder /-
/-- `is_strict_total_order X lt` means that the binary relation `lt` on `X` is a strict total order,
that is, `is_trichotomous X lt` and `is_strict_order X lt`. -/
class IsStrictTotalOrder (α : Type u) (lt : α → α → Prop) extends IsTrichotomous α lt,
  IsStrictOrder α lt : Prop
#align is_strict_total_order IsStrictTotalOrder
-/

/-- Equality is an equivalence relation. -/
instance eq_is_equiv (α : Type u) : IsEquiv α (· = ·)
    where
  symm := @Eq.symm _
  trans := @Eq.trans _
  refl := Eq.refl
#align eq_is_equiv eq_is_equiv

section

variable {α : Type u} {r : α → α → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => r

#print irrefl /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `irrefl [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsIrrefl [`α `r]) "]")
        (Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       (Term.typeSpec ":" («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `a))))
      (Command.declValSimple ":=" (Term.app `IsIrrefl.irrefl [`a]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsIrrefl.irrefl [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsIrrefl.irrefl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `a "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem irrefl [ IsIrrefl α r ] ( a : α ) : ¬ a ≺ a := IsIrrefl.irrefl a
#align irrefl irrefl
-/

#print refl /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `refl [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsRefl [`α `r]) "]")
        (Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       (Term.typeSpec ":" (Init.Algebra.Classes.«term_≺_» `a "≺" `a)))
      (Command.declValSimple ":=" (Term.app `IsRefl.refl [`a]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsRefl.refl [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsRefl.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `a "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem refl [ IsRefl α r ] ( a : α ) : a ≺ a := IsRefl.refl a
#align refl refl
-/

#print trans /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `trans [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsTrans [`α `r]) "]")
        (Term.implicitBinder "{" [`a `b `c] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
         "→"
         (Term.arrow
          (Init.Algebra.Classes.«term_≺_» `b "≺" `c)
          "→"
          (Init.Algebra.Classes.«term_≺_» `a "≺" `c)))))
      (Command.declValSimple
       ":="
       (Term.app `IsTrans.trans [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsTrans.trans [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsTrans.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
       "→"
       (Term.arrow
        (Init.Algebra.Classes.«term_≺_» `b "≺" `c)
        "→"
        (Init.Algebra.Classes.«term_≺_» `a "≺" `c)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Init.Algebra.Classes.«term_≺_» `b "≺" `c)
       "→"
       (Init.Algebra.Classes.«term_≺_» `a "≺" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `a "≺" `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem trans [ IsTrans α r ] { a b c : α } : a ≺ b → b ≺ c → a ≺ c := IsTrans.trans _ _ _
#align trans trans
-/

#print symm /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `symm [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsSymm [`α `r]) "]")
        (Term.implicitBinder "{" [`a `b] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
         "→"
         (Init.Algebra.Classes.«term_≺_» `b "≺" `a))))
      (Command.declValSimple ":=" (Term.app `IsSymm.symm [(Term.hole "_") (Term.hole "_")]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsSymm.symm [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsSymm.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
       "→"
       (Init.Algebra.Classes.«term_≺_» `b "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `b "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem symm [ IsSymm α r ] { a b : α } : a ≺ b → b ≺ a := IsSymm.symm _ _
#align symm symm
-/

#print antisymm /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `antisymm [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsAntisymm [`α `r]) "]")
        (Term.implicitBinder "{" [`a `b] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
         "→"
         (Term.arrow (Init.Algebra.Classes.«term_≺_» `b "≺" `a) "→" («term_=_» `a "=" `b)))))
      (Command.declValSimple
       ":="
       (Term.app `IsAntisymm.antisymm [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsAntisymm.antisymm [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsAntisymm.antisymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
       "→"
       (Term.arrow (Init.Algebra.Classes.«term_≺_» `b "≺" `a) "→" («term_=_» `a "=" `b)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Init.Algebra.Classes.«term_≺_» `b "≺" `a) "→" («term_=_» `a "=" `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `a "=" `b)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Init.Algebra.Classes.«term_≺_» `b "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem antisymm [ IsAntisymm α r ] { a b : α } : a ≺ b → b ≺ a → a = b := IsAntisymm.antisymm _ _
#align antisymm antisymm
-/

#print asymm /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `asymm [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsAsymm [`α `r]) "]")
        (Term.implicitBinder "{" [`a `b] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
         "→"
         («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `a)))))
      (Command.declValSimple ":=" (Term.app `IsAsymm.asymm [(Term.hole "_") (Term.hole "_")]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsAsymm.asymm [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsAsymm.asymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
       "→"
       («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `b "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem asymm [ IsAsymm α r ] { a b : α } : a ≺ b → ¬ b ≺ a := IsAsymm.asymm _ _
#align asymm asymm
-/

#print trichotomous /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `trichotomous [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsTrichotomous [`α `r]) "]")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`a `b]
         [(Term.typeSpec ":" `α)]
         ","
         («term_∨_»
          (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
          "∨"
          («term_∨_» («term_=_» `a "=" `b) "∨" (Init.Algebra.Classes.«term_≺_» `b "≺" `a))))))
      (Command.declValSimple ":=" `IsTrichotomous.trichotomous [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsTrichotomous.trichotomous
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`a `b]
       [(Term.typeSpec ":" `α)]
       ","
       («term_∨_»
        (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
        "∨"
        («term_∨_» («term_=_» `a "=" `b) "∨" (Init.Algebra.Classes.«term_≺_» `b "≺" `a))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
       "∨"
       («term_∨_» («term_=_» `a "=" `b) "∨" (Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_» («term_=_» `a "=" `b) "∨" (Init.Algebra.Classes.«term_≺_» `b "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `b "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  trichotomous
  [ IsTrichotomous α r ] : ∀ a b : α , a ≺ b ∨ a = b ∨ b ≺ a
  := IsTrichotomous.trichotomous
#align trichotomous trichotomous
-/

#print incomp_trans /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `incomp_trans [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsIncompTrans [`α `r]) "]")
        (Term.implicitBinder "{" [`a `b `c] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         («term_∧_»
          («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `b))
          "∧"
          («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
         "→"
         (Term.arrow
          («term_∧_»
           («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `c))
           "∧"
           («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `b)))
          "→"
          («term_∧_»
           («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `c))
           "∧"
           («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `a)))))))
      (Command.declValSimple
       ":="
       (Term.app `IsIncompTrans.incomp_trans [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsIncompTrans.incomp_trans [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsIncompTrans.incomp_trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term_∧_»
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `b))
        "∧"
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
       "→"
       (Term.arrow
        («term_∧_»
         («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `c))
         "∧"
         («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `b)))
        "→"
        («term_∧_»
         («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `c))
         "∧"
         («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `a)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_∧_»
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `c))
        "∧"
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `b)))
       "→"
       («term_∧_»
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `c))
        "∧"
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `a))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `c))
       "∧"
       («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `c "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  incomp_trans
  [ IsIncompTrans α r ] { a b c : α } : ¬ a ≺ b ∧ ¬ b ≺ a → ¬ b ≺ c ∧ ¬ c ≺ b → ¬ a ≺ c ∧ ¬ c ≺ a
  := IsIncompTrans.incomp_trans _ _ _
#align incomp_trans incomp_trans
-/

instance (priority := 90) is_asymm_of_is_trans_of_is_irrefl [IsTrans α r] [IsIrrefl α r] :
    IsAsymm α r :=
  ⟨fun a b h₁ h₂ => absurd (trans h₁ h₂) (irrefl a)⟩
#align is_asymm_of_is_trans_of_is_irrefl is_asymm_of_is_trans_of_is_irrefl

section ExplicitRelationVariants

variable (r)

#print irrefl_of /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `elab_without_expected_type []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `irrefl_of [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsIrrefl [`α `r]) "]")
        (Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       (Term.typeSpec ":" («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `a))))
      (Command.declValSimple ":=" (Term.app `irrefl [`a]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `irrefl [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `irrefl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `a "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ elab_without_expected_type ] theorem irrefl_of [ IsIrrefl α r ] ( a : α ) : ¬ a ≺ a := irrefl a
#align irrefl_of irrefl_of
-/

#print refl_of /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `elab_without_expected_type []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `refl_of [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsRefl [`α `r]) "]")
        (Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       (Term.typeSpec ":" (Init.Algebra.Classes.«term_≺_» `a "≺" `a)))
      (Command.declValSimple ":=" (Term.app `refl [`a]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `refl [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `a "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ elab_without_expected_type ] theorem refl_of [ IsRefl α r ] ( a : α ) : a ≺ a := refl a
#align refl_of refl_of
-/

#print trans_of /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `elab_without_expected_type []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `trans_of [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsTrans [`α `r]) "]")
        (Term.implicitBinder "{" [`a `b `c] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
         "→"
         (Term.arrow
          (Init.Algebra.Classes.«term_≺_» `b "≺" `c)
          "→"
          (Init.Algebra.Classes.«term_≺_» `a "≺" `c)))))
      (Command.declValSimple ":=" `trans [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `trans
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
       "→"
       (Term.arrow
        (Init.Algebra.Classes.«term_≺_» `b "≺" `c)
        "→"
        (Init.Algebra.Classes.«term_≺_» `a "≺" `c)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Init.Algebra.Classes.«term_≺_» `b "≺" `c)
       "→"
       (Init.Algebra.Classes.«term_≺_» `a "≺" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `a "≺" `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ elab_without_expected_type ]
  theorem trans_of [ IsTrans α r ] { a b c : α } : a ≺ b → b ≺ c → a ≺ c := trans
#align trans_of trans_of
-/

#print symm_of /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `elab_without_expected_type []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `symm_of [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsSymm [`α `r]) "]")
        (Term.implicitBinder "{" [`a `b] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
         "→"
         (Init.Algebra.Classes.«term_≺_» `b "≺" `a))))
      (Command.declValSimple ":=" `symm [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
       "→"
       (Init.Algebra.Classes.«term_≺_» `b "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `b "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ elab_without_expected_type ] theorem symm_of [ IsSymm α r ] { a b : α } : a ≺ b → b ≺ a := symm
#align symm_of symm_of
-/

#print asymm_of /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `elab_without_expected_type []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `asymm_of [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsAsymm [`α `r]) "]")
        (Term.implicitBinder "{" [`a `b] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
         "→"
         («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `a)))))
      (Command.declValSimple ":=" `asymm [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `asymm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
       "→"
       («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `b "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ elab_without_expected_type ]
  theorem asymm_of [ IsAsymm α r ] { a b : α } : a ≺ b → ¬ b ≺ a := asymm
#align asymm_of asymm_of
-/

#print total_of /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `elab_without_expected_type []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `total_of [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsTotal [`α `r]) "]")
        (Term.explicitBinder "(" [`a `b] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term_∨_»
         (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
         "∨"
         (Init.Algebra.Classes.«term_≺_» `b "≺" `a))))
      (Command.declValSimple ":=" (Term.app `IsTotal.total [(Term.hole "_") (Term.hole "_")]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsTotal.total [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsTotal.total
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∨_»
       (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
       "∨"
       (Init.Algebra.Classes.«term_≺_» `b "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `b "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ elab_without_expected_type ]
  theorem total_of [ IsTotal α r ] ( a b : α ) : a ≺ b ∨ b ≺ a := IsTotal.total _ _
#align total_of total_of
-/

#print trichotomous_of /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `elab_without_expected_type []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `trichotomous_of [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsTrichotomous [`α `r]) "]")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`a `b]
         [(Term.typeSpec ":" `α)]
         ","
         («term_∨_»
          (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
          "∨"
          («term_∨_» («term_=_» `a "=" `b) "∨" (Init.Algebra.Classes.«term_≺_» `b "≺" `a))))))
      (Command.declValSimple ":=" `trichotomous [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `trichotomous
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`a `b]
       [(Term.typeSpec ":" `α)]
       ","
       («term_∨_»
        (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
        "∨"
        («term_∨_» («term_=_» `a "=" `b) "∨" (Init.Algebra.Classes.«term_≺_» `b "≺" `a))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Init.Algebra.Classes.«term_≺_» `a "≺" `b)
       "∨"
       («term_∨_» («term_=_» `a "=" `b) "∨" (Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_» («term_=_» `a "=" `b) "∨" (Init.Algebra.Classes.«term_≺_» `b "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `b "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ elab_without_expected_type ]
  theorem trichotomous_of [ IsTrichotomous α r ] : ∀ a b : α , a ≺ b ∨ a = b ∨ b ≺ a := trichotomous
#align trichotomous_of trichotomous_of
-/

#print incomp_trans_of /-
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simple `elab_without_expected_type []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `incomp_trans_of [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsIncompTrans [`α `r]) "]")
        (Term.implicitBinder "{" [`a `b `c] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         («term_∧_»
          («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `b))
          "∧"
          («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
         "→"
         (Term.arrow
          («term_∧_»
           («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `c))
           "∧"
           («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `b)))
          "→"
          («term_∧_»
           («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `c))
           "∧"
           («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `a)))))))
      (Command.declValSimple ":=" `incomp_trans [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `incomp_trans
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term_∧_»
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `b))
        "∧"
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
       "→"
       (Term.arrow
        («term_∧_»
         («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `c))
         "∧"
         («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `b)))
        "→"
        («term_∧_»
         («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `c))
         "∧"
         («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `a)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_∧_»
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `b "≺" `c))
        "∧"
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `b)))
       "→"
       («term_∧_»
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `c))
        "∧"
        («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `a))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `a "≺" `c))
       "∧"
       («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (Init.Algebra.Classes.«term_≺_» `c "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Algebra.Classes.«term_≺_» `c "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Algebra.Classes.«term_≺_»', expected 'Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ elab_without_expected_type ]
  theorem
    incomp_trans_of
    [ IsIncompTrans α r ] { a b c : α } : ¬ a ≺ b ∧ ¬ b ≺ a → ¬ b ≺ c ∧ ¬ c ≺ b → ¬ a ≺ c ∧ ¬ c ≺ a
    := incomp_trans
#align incomp_trans_of incomp_trans_of
-/

end ExplicitRelationVariants

end

namespace StrictWeakOrder

section

parameter {α : Type u}{r : α → α → Prop}

-- mathport name: «expr ≺ »
local infixl:50 "≺" => r

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.def
      "def"
      (Command.declId `Equiv [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`a `b] [":" `α] [] ")")]
       [(Term.typeSpec ":" (Term.prop "Prop"))])
      (Command.declValSimple
       ":="
       («term_∧_»
        («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `a "≺" `b))
        "∧"
        («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `a "≺" `b))
       "∧"
       («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `b "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `b "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'StrictWeakOrder.Init.Algebra.Classes.«term_≺_»', expected 'StrictWeakOrder.Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.68'
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
def Equiv ( a b : α ) : Prop := ¬ a ≺ b ∧ ¬ b ≺ a
#align strict_weak_order.equiv StrictWeakOrder.Equiv

parameter [IsStrictWeakOrder α r]

-- mathport name: equiv
local infixl:50 " ≈ " => equiv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `erefl [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       (Term.typeSpec ":" (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `a)))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor "⟨" [(Term.app `irrefl [`a]) "," (Term.app `irrefl [`a])] "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `irrefl [`a]) "," (Term.app `irrefl [`a])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `irrefl [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `irrefl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `irrefl [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `irrefl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'StrictWeakOrder.Init.Algebra.Classes.equiv', expected 'StrictWeakOrder.Init.Algebra.Classes.equiv._@.Init.Algebra.Classes._hyg.115'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem erefl ( a : α ) : a ≈ a := ⟨ irrefl a , irrefl a ⟩
#align strict_weak_order.erefl StrictWeakOrder.erefl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `esymm [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `b)
         "→"
         (StrictWeakOrder.Init.Algebra.Classes.equiv `b " ≈ " `a))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]
         []
         "=>"
         (Term.anonymousCtor "⟨" [`h₂ "," `h₁] "⟩")))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]
        []
        "=>"
        (Term.anonymousCtor "⟨" [`h₂ "," `h₁] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`h₂ "," `h₁] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `b)
       "→"
       (StrictWeakOrder.Init.Algebra.Classes.equiv `b " ≈ " `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (StrictWeakOrder.Init.Algebra.Classes.equiv `b " ≈ " `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'StrictWeakOrder.Init.Algebra.Classes.equiv', expected 'StrictWeakOrder.Init.Algebra.Classes.equiv._@.Init.Algebra.Classes._hyg.115'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem esymm { a b : α } : a ≈ b → b ≈ a := fun ⟨ h₁ , h₂ ⟩ => ⟨ h₂ , h₁ ⟩
#align strict_weak_order.esymm StrictWeakOrder.esymm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `etrans [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b `c] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `b)
         "→"
         (Term.arrow
          (StrictWeakOrder.Init.Algebra.Classes.equiv `b " ≈ " `c)
          "→"
          (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `c)))))
      (Command.declValSimple ":=" `incomp_trans [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `incomp_trans
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `b)
       "→"
       (Term.arrow
        (StrictWeakOrder.Init.Algebra.Classes.equiv `b " ≈ " `c)
        "→"
        (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `c)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (StrictWeakOrder.Init.Algebra.Classes.equiv `b " ≈ " `c)
       "→"
       (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'StrictWeakOrder.Init.Algebra.Classes.equiv', expected 'StrictWeakOrder.Init.Algebra.Classes.equiv._@.Init.Algebra.Classes._hyg.115'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem etrans { a b c : α } : a ≈ b → b ≈ c → a ≈ c := incomp_trans
#align strict_weak_order.etrans StrictWeakOrder.etrans

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `not_lt_of_equiv [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `b)
         "→"
         («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `a "≺" `b)))))
      (Command.declValSimple
       ":="
       (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.proj `h "." (fieldIdx "1"))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.proj `h "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `h "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `b)
       "→"
       («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `a "≺" `b)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `a "≺" `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `a "≺" `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'StrictWeakOrder.Init.Algebra.Classes.«term_≺_»', expected 'StrictWeakOrder.Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.68'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem not_lt_of_equiv { a b : α } : a ≈ b → ¬ a ≺ b := fun h => h . 1
#align strict_weak_order.not_lt_of_equiv StrictWeakOrder.not_lt_of_equiv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `not_lt_of_equiv' [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" `α] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `b)
         "→"
         («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `b "≺" `a)))))
      (Command.declValSimple
       ":="
       (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.proj `h "." (fieldIdx "2"))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.proj `h "." (fieldIdx "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `h "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (StrictWeakOrder.Init.Algebra.Classes.equiv `a " ≈ " `b)
       "→"
       («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `b "≺" `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `b "≺" `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (StrictWeakOrder.Init.Algebra.Classes.«term_≺_» `b "≺" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'StrictWeakOrder.Init.Algebra.Classes.«term_≺_»', expected 'StrictWeakOrder.Init.Algebra.Classes.term_≺_._@.Init.Algebra.Classes._hyg.68'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem not_lt_of_equiv' { a b : α } : a ≈ b → ¬ b ≺ a := fun h => h . 2
#align strict_weak_order.not_lt_of_equiv' StrictWeakOrder.not_lt_of_equiv'

instance is_equiv : IsEquiv α equiv where
  refl := erefl
  trans := @etrans
  symm := @esymm
#align strict_weak_order.is_equiv StrictWeakOrder.is_equiv

end

-- mathport name: «expr ≈[ ] »
notation:50 -- Notation for the equivalence relation induced by lt
a " ≈[" lt "]" b:50 => @Equiv _ lt a b

end StrictWeakOrder

theorem is_strict_weak_order_of_is_total_preorder {α : Type u} {le : α → α → Prop}
    {lt : α → α → Prop} [DecidableRel le] [s : IsTotalPreorder α le] (h : ∀ a b, lt a b ↔ ¬le b a) :
    IsStrictWeakOrder α lt :=
  { trans := fun a b c hab hbc =>
      have nba : ¬le b a := Iff.mp (h _ _) hab
      have ncb : ¬le c b := Iff.mp (h _ _) hbc
      have hab : le a b := Or.resolve_left (total_of le b a) nba
      have nca : ¬le c a := fun hca : le c a =>
        have hcb : le c b := trans_of le hca hab
        absurd hcb ncb
      Iff.mpr (h _ _) nca
    irrefl := fun a hlt => absurd (refl_of le a) (Iff.mp (h _ _) hlt)
    incomp_trans := fun a b c ⟨nab, nba⟩ ⟨nbc, ncb⟩ =>
      have hba : le b a := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) nab)
      have hab : le a b := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) nba)
      have hcb : le c b := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) nbc)
      have hbc : le b c := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) ncb)
      have hac : le a c := trans_of le hab hbc
      have hca : le c a := trans_of le hcb hba
      And.intro (fun n => absurd hca (Iff.mp (h _ _) n)) fun n => absurd hac (Iff.mp (h _ _) n) }
#align is_strict_weak_order_of_is_total_preorder is_strict_weak_order_of_is_total_preorder

#print lt_of_lt_of_incomp /-
theorem lt_of_lt_of_incomp {α : Type u} {lt : α → α → Prop} [IsStrictWeakOrder α lt]
    [DecidableRel lt] : ∀ {a b c}, lt a b → ¬lt b c ∧ ¬lt c b → lt a c :=
  fun a b c hab ⟨nbc, ncb⟩ =>
  have nca : ¬lt c a := fun hca => absurd (trans_of lt hca hab) ncb
  Decidable.by_contradiction fun nac : ¬lt a c =>
    have : ¬lt a b ∧ ¬lt b a := incomp_trans_of lt ⟨nac, nca⟩ ⟨ncb, nbc⟩
    absurd hab this.1
#align lt_of_lt_of_incomp lt_of_lt_of_incomp
-/

#print lt_of_incomp_of_lt /-
theorem lt_of_incomp_of_lt {α : Type u} {lt : α → α → Prop} [IsStrictWeakOrder α lt]
    [DecidableRel lt] : ∀ {a b c}, ¬lt a b ∧ ¬lt b a → lt b c → lt a c :=
  fun a b c ⟨nab, nba⟩ hbc =>
  have nca : ¬lt c a := fun hca => absurd (trans_of lt hbc hca) nba
  Decidable.by_contradiction fun nac : ¬lt a c =>
    have : ¬lt b c ∧ ¬lt c b := incomp_trans_of lt ⟨nba, nab⟩ ⟨nac, nca⟩
    absurd hbc this.1
#align lt_of_incomp_of_lt lt_of_incomp_of_lt
-/

#print eq_of_incomp /-
theorem eq_of_incomp {α : Type u} {lt : α → α → Prop} [IsTrichotomous α lt] {a b} :
    ¬lt a b ∧ ¬lt b a → a = b := fun ⟨nab, nba⟩ =>
  match trichotomous_of lt a b with
  | Or.inl hab => absurd hab nab
  | Or.inr (Or.inl hab) => hab
  | Or.inr (Or.inr hba) => absurd hba nba
#align eq_of_incomp eq_of_incomp
-/

#print eq_of_eqv_lt /-
theorem eq_of_eqv_lt {α : Type u} {lt : α → α → Prop} [IsTrichotomous α lt] {a b} :
    a ≈[lt]b → a = b :=
  eq_of_incomp
#align eq_of_eqv_lt eq_of_eqv_lt
-/

#print incomp_iff_eq /-
theorem incomp_iff_eq {α : Type u} {lt : α → α → Prop} [IsTrichotomous α lt] [IsIrrefl α lt] (a b) :
    ¬lt a b ∧ ¬lt b a ↔ a = b :=
  Iff.intro eq_of_incomp fun hab => Eq.subst hab (And.intro (irrefl_of lt a) (irrefl_of lt a))
#align incomp_iff_eq incomp_iff_eq
-/

#print eqv_lt_iff_eq /-
theorem eqv_lt_iff_eq {α : Type u} {lt : α → α → Prop} [IsTrichotomous α lt] [IsIrrefl α lt] (a b) :
    a ≈[lt]b ↔ a = b :=
  incomp_iff_eq a b
#align eqv_lt_iff_eq eqv_lt_iff_eq
-/

#print not_lt_of_lt /-
theorem not_lt_of_lt {α : Type u} {lt : α → α → Prop} [IsStrictOrder α lt] {a b} :
    lt a b → ¬lt b a := fun h₁ h₂ => absurd (trans_of lt h₁ h₂) (irrefl_of lt _)
#align not_lt_of_lt not_lt_of_lt
-/

