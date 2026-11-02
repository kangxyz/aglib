/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedSections
public import Aglib.Algebra.Homology.RightDerived.Represented

/-!
# Represented Ext and actual right-derived sections

The comparison uses the original injective resolution and the native
right-derived functor, through its actual Hom complex. It does not define
right-derived sections by declaring them to be Ext.
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CochainComplex CochainComplex.HomComplex

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [EnoughInjectives C]

/-- The original represented Ext agrees with the native right-derived represented functor. -/
abbrev extRightDerivedRepresentedAddEquiv (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃+
      (((preadditiveCoyoneda.obj (op X)).rightDerived n).obj Y) :=
  CategoryTheory.Abelian.extRightDerivedRepresentedAddEquiv X Y n

/-- The shared native constructor has the original module-comparison value,
including its original Hom-complex and extension-by-zero maps. -/
theorem extRightDerivedRepresentedAddEquiv_eq_original (X Y : C) (n : ℕ) :
    extRightDerivedRepresentedAddEquiv X Y n = by
  let I := injectiveResolution Y
  let G := preadditiveCoyoneda.obj (op X)
  let e : ((G.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≅
      (((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extend
        ComplexShape.embeddingUpNat) :=
    I.cocomplex.mapExtendIso G ComplexShape.embeddingUpNat
  exact I.extAddEquivCohomologyClass.trans
    ((HomComplex.homologyAddEquiv _ _ (n : ℤ)).symm.trans
      ((((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) (n : ℤ)).mapIso
        (singleHomComplexIso X I.cochainComplex)).addCommGroupIsoToAddEquiv).trans
        ((((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) (n : ℤ)).mapIso
          e).addCommGroupIsoToAddEquiv).trans
          ((((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (j := n) rfl).addCommGroupIsoToAddEquiv.trans
            (I.isoRightDerivedObj G n).symm.addCommGroupIsoToAddEquiv)))) := by
  ext x
  rfl

end CategoryTheory.Sheaf.ModuleCoefficients
