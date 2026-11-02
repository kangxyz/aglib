/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingAdjunction
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.UnderlyingComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactMateCube

/-!
# Original module-derived exchange under scalar forgetting

The original module exchange becomes the original abelian exchange through the
specified inverse- and direct-image comparisons. The source cube descends from
its actual coefficient-level equation, and the exchange equation follows by
native mate pasting. No proper-base-change or exchange-invertibility premise is
used or concluded.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wMX wMS wMX' wMS' wAX wAS wAX' wAS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wAX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wAS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- Scalar forgetting preserves the same original derived exchange. The conclusion
is the literal original comparison equation for every derived coefficient object,
with all six transformations specified below; it is not an additional hypothesis.
Exact-source normalization and mate pasting occur before specialization. -/
theorem moduleDerivedBaseChangeMap_underlying :
    HorizontalMateCubeEquation
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom
      (moduleDerivedBaseChangeMap Λ f f' g g' h)
      (derivedBaseChangeMap f f' g g' h)
      (moduleDerivedInverseImageUnderlyingIso Λ g).inv
      (moduleDerivedInverseImageUnderlyingIso Λ g').inv := by
  exact rightDerivedFunctorPlus_mateCube_of_whole
    (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
    (inverseImageAdjunction f) (inverseImageAdjunction f')
    (moduleInverseImageUnderlyingIso Λ f) (moduleInverseImageUnderlyingIso Λ f')
    (moduleInverseImageUnderlyingIso Λ g) (moduleInverseImageUnderlyingIso Λ g')
    (moduleInverseImageSquareIso Λ f f' g g' h) (inverseImageSquareIso f f' g g' h)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ f).inv)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ f').inv)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ g).inv)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ g').inv)
    (moduleDerivedInverseImageUnderlyingIso_exactComparison Λ f)
    (moduleDerivedInverseImageUnderlyingIso_exactComparison Λ f')
    (moduleDerivedInverseImageSquareIso_exactComparison Λ f f' g g' h)
    (derivedInverseImageSquareIso_exactComparison f f' g g' h)
    (moduleDerivedInverseImageUnderlyingIso_exactComparison Λ g)
    (moduleDerivedInverseImageUnderlyingIso_exactComparison Λ g')
    (moduleInverseImageSquareIso_underlying_whole Λ f f' g g' h)
    (moduleDerivedDirectImageUnderlyingIso Λ f).hom
    (moduleDerivedDirectImageUnderlyingIso Λ f').hom
    (moduleDerivedBaseChangeMap Λ f f' g g' h)
    (derivedBaseChangeMap f f' g g' h)
    (mate_moduleDerivedInverseImageUnderlyingIso_inv Λ f)
    (mate_moduleDerivedInverseImageUnderlyingIso_inv Λ f') rfl rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
