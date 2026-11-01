/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenMate
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Composition

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

/-- The map uses only the specified original Cartesian mate and original compositors. -/
def moduleUnboundedCartesianCompositionUnderlyingMap :=
  imageCompositionMap
    (K := @moduleUnboundedDerivedLowerShriek X F.Xbar F.j _ Λ _ hX hF)
    (J := @moduleUnboundedDerivedLowerShriek X C.sourceCompactification.Xbar
        C.sourceCompactification.j _ Λ _ hX hFG)
    (L := @moduleUnboundedDerivedLowerShriek F.Xbar C.sourceCompactification.Xbar m _ Λ _ hF hFG)
    (Q := @moduleUnboundedDerivedDirectImage Λ _ Y F.Xbar F.p hY hF)
    (I := @moduleUnboundedDerivedLowerShriek Y C.targetCompactification.Xbar
      C.targetCompactification.j _ Λ _ hY hG)
    (R := @moduleUnboundedDerivedDirectImage Λ _ C.targetCompactification.Xbar
      C.sourceCompactification.Xbar C.sourceCompactification.p hG hFG)
    (P := @moduleUnboundedDerivedDirectImage Λ _ Z C.targetCompactification.Xbar
      C.targetCompactification.p hZ hG)
    (S := @moduleUnboundedDerivedDirectImage Λ _ Z C.sourceCompactification.Xbar
      (C.sourceCompactification.p ≫ C.targetCompactification.p) hZ hFG)
    (@moduleUnboundedProperOpenMate F.Xbar Y C.sourceCompactification.Xbar
      C.targetCompactification.Xbar F.p m C.targetCompactification.j
      C.sourceCompactification.p _ _ sq.flip Λ _ hF hY hFG hG)
    (@moduleUnboundedDerivedLowerShriekOverIso Λ _ X F.Xbar
      C.sourceCompactification.Xbar hX hF hFG F.j m C.sourceCompactification.j _ _ _ hj)
    (@moduleUnboundedDerivedDirectImageCompIso Λ _ Z C.targetCompactification.Xbar
      C.sourceCompactification.Xbar C.targetCompactification.p
      C.sourceCompactification.p hZ hG hFG).symm


end AlgebraicGeometry.Scheme.EtaleCohomology
