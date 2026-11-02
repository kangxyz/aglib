/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionMap
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModel

/-! # Original composition through a specified Cartesian first compactification

The first ambient need not be the chosen pullback object. The map is built
from the same original proper/open mate, open compositor and proper compositor.
The canonical pullback presentation is compared to the existing map separately.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wF wG wFG
variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  (m : F.Xbar ⟶ C.sourceCompactification.Xbar) [IsOpenImmersion m]
  (sq : IsPullback m F.p C.sourceCompactification.p C.targetCompactification.j)
  (hj : F.j ≫ m = C.sourceCompactification.j)
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ))
  (hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ))
  (hF : HasDerivedCategory.{wF} (ModuleSheaf F.Xbar Λ))
  (hG : HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ))
  (hFG : HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ))

/-- The specified original open compositor, followed by the actual source equality. -/
def moduleUnboundedCartesianCompositionOpenIso :
    @moduleUnboundedDerivedLowerShriek X F.Xbar F.j _ Λ _ hX hF ⋙
      @moduleUnboundedDerivedLowerShriek F.Xbar C.sourceCompactification.Xbar m _ Λ _ hF hFG ≅
    @moduleUnboundedDerivedLowerShriek X C.sourceCompactification.Xbar
      C.sourceCompactification.j _ Λ _ hX hFG :=
  (@moduleUnboundedDerivedLowerShriekCompIso Λ _ C.sourceCompactification.Xbar F.Xbar X
    m F.j _ _ hFG hF hX).symm ≪≫
    eqToIso (@moduleUnboundedDerivedLowerShriek_congr X C.sourceCompactification.Xbar Λ _ hX hFG
      (F.j ≫ m) C.sourceCompactification.j _ _ hj)

end AlgebraicGeometry.Scheme.EtaleCohomology
