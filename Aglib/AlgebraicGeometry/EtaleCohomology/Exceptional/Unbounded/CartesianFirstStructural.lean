/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianFirstRectangle
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRefinementDirectImage

/-! # The original proper-image face with unchanged target and total compactifications -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wZ wG wFG
variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (C : Hom.CompactifiedComposition f g) (Λ : Type (u + 1)) [Ring Λ]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [hG : HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ)]
  [hFG : HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ)]

/-- Original proper compositors and identity refinements satisfy the structural face. -/
theorem moduleUnboundedCartesianFirstStructuralEquation :
    ImageCompositionStructuralEquation
      (moduleUnboundedDerivedRefinementDirectImageIso Λ (𝟙 C.targetCompactification))
      (moduleUnboundedProperOpenRefinementTargetIso Λ C.sourceCompactification.p
        C.sourceCompactification.p (𝟙 C.sourceCompactification.Xbar)
        (𝟙 C.targetCompactification.Xbar) (unboundedCartesianFirstProperSquare C))
      (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm
      (moduleUnboundedDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).symm
      (@moduleUnboundedDerivedRefinementDirectImageIso Λ _ X Z (f ≫ g) hZ
        C.composite C.composite (𝟙 C.composite) hFG hFG) :=
  moduleUnboundedDerivedDirectImageOverIso_rectangle Λ
    C.sourceCompactification.p C.sourceCompactification.p
    (𝟙 C.sourceCompactification.Xbar) (𝟙 C.targetCompactification.Xbar)
    C.targetCompactification.p C.targetCompactification.p
    (unboundedCartesianFirstProperSquare C) (Category.id_comp C.targetCompactification.p)
    (Category.id_comp (C.sourceCompactification.p ≫ C.targetCompactification.p))

end AlgebraicGeometry.Scheme.EtaleCohomology
