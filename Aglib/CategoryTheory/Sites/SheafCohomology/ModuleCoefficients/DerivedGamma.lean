/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.RightDerived.Postcomp
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedComparisonFactory
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.RepresentedSections
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Evaluation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Native derived terminal sections

The functor being derived is native module evaluation at the terminal object.
Exact scalar forgetting commutes with its cohomology, without claiming that
scalar forgetting preserves injective objects.
-/

@[expose] public noncomputable section

universe u v u₁ v₁ u₂ v₂ r w e

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

section Abstract

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]

/-- Exact postcomposition commutes with the actual homology of a cochain complex. -/
abbrev cochainHomologyPostcompIso (G : D ⥤ E) [G.Additive] [G.PreservesHomology]
    (n : ℕ) :
    G.mapHomologicalComplex (.up ℕ) ⋙ HomologicalComplex.homologyFunctor E _ n ≅
      HomologicalComplex.homologyFunctor D _ n ⋙ G :=
  CategoryTheory.Functor.cochainHomologyPostcompIso G n

/-- The canonical comparison for deriving a natural isomorphism of additive functors. -/
abbrev rightDerivedNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n :=
  CategoryTheory.Functor.rightDerivedNatIsoOfAdditive α n

/-- Compute exact postcomposition on the original chosen injective resolution. -/
abbrev rightDerivedPostcompObjIso (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [G.PreservesHomology] (n : ℕ) (X : C) :
    ((F ⋙ G).rightDerived n).obj X ≅ G.obj ((F.rightDerived n).obj X) :=
  CategoryTheory.Functor.rightDerivedPostcompObjIso F G n X

/-- Exact postcomposition commutes naturally with native right-derived functors. -/
abbrev rightDerivedPostcompIso (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [G.PreservesHomology] (n : ℕ) :
    (F ⋙ G).rightDerived n ≅ F.rightDerived n ⋙ G :=
  CategoryTheory.Functor.rightDerivedPostcompIso F G n

end Abstract

section Terminal

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [EnoughInjectives (SheafOfModules.{max u v r w} R)]

/-- Native derived terminal module evaluation, after exact scalar forgetting,
is naturally identified with the derived represented additive functor. -/
abbrev derivedTerminalSectionsIso (n : ℕ) :
    (SheafOfModules.evaluation.{max u v r w} R (op T)).rightDerived n ⋙
        forget₂ (ModuleCat.{max u v r w} (R.obj.obj (op T)))
          AddCommGrpCat.{max u v r w} ≅
      (preadditiveCoyoneda.obj
        (op (SheafOfModules.liftedUnit.{u, v, max u v w, r} R))).rightDerived n :=
  SheafOfModules.derivedRepresentedGammaTerminalIso hT R n

variable [HasExt.{e} (SheafOfModules.{max u v r w} R)]

/-- Native derived module sections agree additively with the original represented Ext.
The source is the original module-valued right-derived evaluation, not a definition by Ext. -/
def derivedTerminalSectionsExtAddEquiv
    (M : SheafOfModules.{max u v r w} R) (n : ℕ) :
    ((SheafOfModules.evaluation R (op T)).rightDerived n).obj M ≃+
      Ext.{e} (SheafOfModules.liftedUnit.{u, v, max u v w, r} R) M n :=
  representedDerivedModuleAddEquiv
    (SheafOfModules.liftedUnit.{u, v, max u v w, r} R)
    ((SheafOfModules.evaluation.{max u v r w} R (op T)).rightDerived n) n
    (derivedTerminalSectionsIso.{u, v, r, w} hT R n) M

end Terminal

end CategoryTheory.Sheaf.ModuleCoefficients
