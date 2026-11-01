/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianCompositionMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementHorizontal

/-! # The original horizontal face for a refined Cartesian first presentation -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wF wC wFG
variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [QuasiCompact f] [QuasiCompact g]
  (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  (m : F.Xbar ⟶ C.sourceCompactification.Xbar) [IsOpenImmersion m]
  (a : F ⟶ C.first)
  (sqMid : IsPullback m a.hom (𝟙 C.sourceCompactification.Xbar) C.middleOpen)
  (hj : F.j ≫ m = C.sourceCompactification.j)
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hF : HasDerivedCategory.{wF} (ModuleSheaf F.Xbar Λ))
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C.first.Xbar Λ))
  (hFG : HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ))

/-- The original source refinement and total identity unit satisfy the horizontal mate face,
with the actual canonical and specified Cartesian open compositors unchanged. -/
theorem moduleCartesianCompositionRefinementHorizontal :
    UnitMateHorizontalEquation
      (@moduleDerivedRefinementComparison X Y f _ F C.first a Λ _ hX hF hC)
      (@moduleDerivedRefinementComparison X Z (f ≫ g) _ C.composite C.composite
        (𝟙 C.composite) Λ _ hX hFG hFG)
      (@moduleProperOpenMate Λ _ C.first.Xbar F.Xbar C.sourceCompactification.Xbar
        C.sourceCompactification.Xbar C.middleOpen m a.hom
        (𝟙 C.sourceCompactification.Xbar) _ _ sqMid.flip hC hF hFG hFG)
      (moduleCartesianCompositionOpenIso C C.first C.middleOpen C.first_j_middleOpen
        Λ hX hC hFG).symm
      (moduleCartesianCompositionOpenIso C F m hj Λ hX hF hFG).symm :=
  @moduleDerivedProperRefinementComparison_hComp_transport Λ _ X
    F.Xbar C.first.Xbar C.sourceCompactification.Xbar C.sourceCompactification.Xbar
    F.j C.first.j m C.middleOpen _ _ _ _ a.hom (𝟙 C.sourceCompactification.Xbar)
    (Hom.DenseCompactification.isPullback_open a) sqMid hX hF hC hFG hFG
    C.sourceCompactification.j C.sourceCompactification.j _ _ hj C.first_j_middleOpen
    (Hom.DenseCompactification.isPullback_open (𝟙 C.composite))

end AlgebraicGeometry.Scheme.EtaleCohomology
