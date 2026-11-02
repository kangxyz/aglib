/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.PlusAdjunctionMate
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.PlusExactSquare
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.SpecifiedMateCube

/-!
# The original unbounded exchange restricts to the original bounded-below exchange

The comparison is an equation of actual arrows obtained from the exact-square
cube and the original adjunction-unit equations. It does not identify arrows
by homology or by bounded-below testing of arbitrary unbounded transformations.
No properness or invertibility assertion is made here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wX' wS'

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The fixed plus/full exact comparisons preserve the original inverse-image square. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_plus
    (K : DerivedCategory.Plus (ModuleSheaf S Λ)) :
    (moduleUnboundedDerivedInverseImage Λ f').map
        ((moduleDerivedInverseImageCompιIso Λ g).inv.app K) ≫
      (moduleDerivedInverseImageCompιIso Λ f').inv.app
        ((moduleDerivedInverseImage Λ g).obj K) ≫
      DerivedCategory.Plus.ι.map
        ((moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom.app K) =
    (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom.app K.obj ≫
      (moduleUnboundedDerivedInverseImage Λ g').map
        ((moduleDerivedInverseImageCompιIso Λ f).inv.app K) ≫
      (moduleDerivedInverseImageCompιIso Λ g').inv.app
        ((moduleDerivedInverseImage Λ f).obj K) :=
  Functor.mapDerivedCategorySquareIso_plus
    (moduleInverseImage f Λ) (moduleInverseImage g' Λ)
    (moduleInverseImage g Λ) (moduleInverseImage f' Λ)
    (moduleInverseImageSquareIso Λ f f' g g' h)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom)
    (moduleDerivedInverseImageSquareIso_exactComparison Λ f f' g g' h) K

/-- The actual unbounded exchange restricts to the same bounded-below mate,
through the specified original direct- and inverse-image comparisons. -/
theorem moduleUnboundedDerivedBaseChangeMap_plus
    (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleUnboundedDerivedInverseImage Λ g).map
        ((moduleDerivedDirectImageCompιIso Λ f).hom.app K) ≫
      (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' h).app K.obj ≫
      (moduleUnboundedDerivedDirectImage Λ f').map
        ((moduleDerivedInverseImageCompιIso Λ g').inv.app K) =
    (moduleDerivedInverseImageCompιIso Λ g).inv.app
        ((moduleDerivedDirectImage Λ f).obj K) ≫
      DerivedCategory.Plus.ι.map ((moduleDerivedBaseChangeMap Λ f f' g g' h).app K) ≫
      (moduleDerivedDirectImageCompιIso Λ f').hom.app
        ((moduleDerivedInverseImage Λ g').obj K) :=
  horizontalMateCubeEquation_of_specified_mates
    (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ f')
    (moduleUnboundedDerivedAdjunction Λ f) (moduleUnboundedDerivedAdjunction Λ f')
    (moduleDerivedInverseImageCompιIso Λ f).inv
    (moduleDerivedInverseImageCompιIso Λ f').inv
    (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom
    (moduleUnboundedDerivedInverseImageSquareIso Λ f f' g g' h).hom
    (moduleDerivedInverseImageCompιIso Λ g).inv
    (moduleDerivedInverseImageCompιIso Λ g').inv
    (moduleDerivedDirectImageCompιIso Λ f).hom
    (moduleDerivedDirectImageCompιIso Λ f').hom
    (moduleDerivedBaseChangeMap Λ f f' g g' h)
    (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' h)
    (moduleInverseImageAdjunction f Λ).unboundedRightDerivedAdjunction_plus_mate
    (moduleInverseImageAdjunction f' Λ).unboundedRightDerivedAdjunction_plus_mate
    rfl rfl (moduleUnboundedDerivedInverseImageSquareIso_plus Λ f f' g g' h) K

end AlgebraicGeometry.Scheme.EtaleCohomology
