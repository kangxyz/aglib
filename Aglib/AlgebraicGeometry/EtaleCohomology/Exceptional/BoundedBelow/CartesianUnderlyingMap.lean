/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionPrewhisker
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianCompositionMap
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementAdapters

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
def moduleCartesianCompositionUnderlyingMap :=
  imageCompositionMap
    (K := @moduleDerivedLowerShriek X F.Xbar F.j _ Λ _ hX hF)
    (J := @moduleDerivedLowerShriek X C.sourceCompactification.Xbar
        C.sourceCompactification.j _ Λ _ hX hFG)
    (L := @moduleDerivedLowerShriek F.Xbar C.sourceCompactification.Xbar m _ Λ _ hF hFG)
    (Q := @moduleDerivedDirectImage Y Λ _ F.Xbar F.p hY hF)
    (I := @moduleDerivedLowerShriek Y C.targetCompactification.Xbar
      C.targetCompactification.j _ Λ _ hY hG)
    (R := @moduleDerivedDirectImage C.targetCompactification.Xbar Λ _
      C.sourceCompactification.Xbar C.sourceCompactification.p hG hFG)
    (P := @moduleDerivedDirectImage Z Λ _ C.targetCompactification.Xbar
      C.targetCompactification.p hZ hG)
    (S := @moduleDerivedDirectImage Z Λ _ C.sourceCompactification.Xbar
      (C.sourceCompactification.p ≫ C.targetCompactification.p) hZ hFG)
    (@moduleProperOpenMate Λ _ Y F.Xbar C.targetCompactification.Xbar
      C.sourceCompactification.Xbar C.targetCompactification.j m F.p
      C.sourceCompactification.p _ _ sq.flip hY hF hG hFG)
    (moduleCartesianCompositionOpenIso C F m hj Λ hX hF hFG)
    (@moduleDerivedDirectImageCompIso Λ _ Z C.targetCompactification.Xbar
      C.sourceCompactification.Xbar C.targetCompactification.p
      C.sourceCompactification.p hZ hG hFG).symm


/-- The existing original torsion-source map is exactly this underlying map restricted. -/
theorem moduleCartesianCompositionMap_underlying :
    moduleCartesianCompositionMap C F m sq hj Λ hX hY hZ hF hG hFG =
      Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
        (moduleCartesianCompositionUnderlyingMap C F m sq hj Λ hX hY hZ hF hG hFG) :=
  imageCompositionMap_whiskerLeft _ _ _ _

end AlgebraicGeometry.Scheme.EtaleCohomology
