/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRefinementFaces
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenRefinementRectangle
public import Aglib.CategoryTheory.Adjunction.NaturalPastedRectangleSource

/-! # The original vertical face when a Cartesian first presentation is refined -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wY wF wC wG wFG
variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (C : Hom.CompactifiedComposition f g)

/-- Both unchanged proper sides retain their actual identity morphisms. -/
theorem unboundedCartesianFirstProperSquare :
    (𝟙 C.sourceCompactification.Xbar) ≫ C.sourceCompactification.p =
      C.sourceCompactification.p ≫ 𝟙 C.targetCompactification.Xbar :=
  (Category.id_comp _).trans (Category.comp_id _).symm

variable [QuasiCompact g] (F : Hom.DenseCompactification f)
  (m : F.Xbar ⟶ C.sourceCompactification.Xbar) [IsOpenImmersion m]
  (sq : IsPullback m F.p C.sourceCompactification.p C.targetCompactification.j)
  (a : F ⟶ C.first)
  (sqMid : IsPullback m a.hom (𝟙 C.sourceCompactification.Xbar) C.middleOpen)
  (Λ : Type (u + 1)) [Ring Λ]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hF : HasDerivedCategory.{wF} (ModuleSheaf F.Xbar Λ)]
  [hC : HasDerivedCategory.{wC} (ModuleSheaf C.first.Xbar Λ)]
  [hG : HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ)]
  [hFG : HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ)]

/-- The original target-refinement unit contracts the actual pasted mate rectangle. -/
theorem moduleUnboundedCartesianFirstRefinementRectangle :
    NaturalRefinementRectangleEquation
      (moduleUnboundedProperOpenMate C.first.p C.middleOpen C.targetCompactification.j
        C.sourceCompactification.p C.isPullback_middleOpen.flip Λ)
      (moduleUnboundedProperOpenMate a.hom m C.middleOpen (𝟙 C.sourceCompactification.Xbar)
        sqMid.flip Λ)
      (moduleUnboundedDerivedRefinementComparison (𝟙 C.targetCompactification) Λ)
      (moduleUnboundedProperOpenMate F.p m C.targetCompactification.j C.sourceCompactification.p
        sq.flip Λ)
      (moduleUnboundedDerivedRefinementDirectImageIso Λ a)
      (moduleUnboundedProperOpenRefinementTargetIso Λ C.sourceCompactification.p
        C.sourceCompactification.p (𝟙 C.sourceCompactification.Xbar)
        (𝟙 C.targetCompactification.Xbar) (unboundedCartesianFirstProperSquare C)) := by
  exact naturalPastedRectangle_contract_identitySource
    (moduleUnboundedDerivedAdjunction Λ (𝟙 Y))
    (moduleUnboundedDerivedAdjunction Λ (𝟙 C.targetCompactification.Xbar))
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (𝟙 Y)
        C.targetCompactification.j C.targetCompactification.j
        (𝟙 C.targetCompactification.Xbar)
        (Hom.DenseCompactification.isPullback_open (𝟙 C.targetCompactification)).flip Λ).hom)
    (moduleUnboundedDerivedDirectImageIdIso Λ Y)
    (moduleUnboundedDerivedRefinementComparison (𝟙 C.targetCompactification) Λ)
    (moduleUnboundedDerivedProperRefinementComparison_identitySourceMate
      C.targetCompactification.j C.targetCompactification.j (𝟙 C.targetCompactification.Xbar)
      (Hom.DenseCompactification.isPullback_open (𝟙 C.targetCompactification)) Λ)
    _ _ _ _ _ _ rfl
    (moduleUnboundedProperOpenMate_refinement_rectangle Λ
      C.targetCompactification.j C.targetCompactification.j m C.middleOpen
      F.p C.first.p C.sourceCompactification.p C.sourceCompactification.p
      a.hom (𝟙 C.sourceCompactification.Xbar) (𝟙 C.targetCompactification.Xbar)
      sq C.isPullback_middleOpen sqMid
      (Hom.DenseCompactification.isPullback_open (𝟙 C.targetCompactification))
      a.base_fac (unboundedCartesianFirstProperSquare C))

end AlgebraicGeometry.Scheme.EtaleCohomology
