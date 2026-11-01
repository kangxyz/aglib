/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenBaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementDirectImage
public import Aglib.CategoryTheory.Adjunction.RefinementOuterComparison

/-! # The canonical `j! → Rj*` comparison respects the original refinement unit

The two ambient derived models are independent. Properness and torsion are
not needed for this naturality equation; all comparisons are the original maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wC wD
variable (Λ : Type (u + 1)) [Ring Λ]
  {U C D : Scheme.{u}} (jC : U ⟶ C) (jD : U ⟶ D) (a : C ⟶ D)
  [IsOpenImmersion jC] [IsOpenImmersion jD]
  (h : IsPullback jC (𝟙 U) a jD)
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]

omit [IsOpenImmersion jC] [IsOpenImmersion jD] in
/-- The original image square contracts to the original over-base triangle. -/
theorem moduleUnboundedDerivedDirectImageSquareIso_refinement :
    moduleUnboundedDerivedDirectImageSquareIso Λ a (𝟙 U) jD jC h.flip.w ≪≫
      Functor.isoWhiskerRight (moduleUnboundedDerivedDirectImageIdIso Λ U)
        (moduleUnboundedDerivedDirectImage Λ jD) ≪≫
      Functor.leftUnitor (moduleUnboundedDerivedDirectImage Λ jD) =
    moduleUnboundedDerivedDirectImageOverIso Λ jD a jC (h.w.trans (Category.id_comp jD)) := by
  simp only [moduleUnboundedDerivedDirectImageSquareIso, Iso.trans_assoc]
  rw [moduleUnboundedDerivedDirectImageCompIso_comp_id]
  simp only [moduleUnboundedDerivedDirectImageOverIso, eqToIso_trans]

/-- The original Cartesian refinement unit preserves the canonical outer-adjoint comparison. -/
theorem moduleUnboundedDerivedProperRefinementComparison_toDirectImage_naturality :
    moduleUnboundedDerivedProperRefinementComparison jC jD a h Λ ≫
      Functor.whiskerRight (moduleUnboundedLowerShriekToDirectImage Λ jC)
        (moduleUnboundedDerivedDirectImage Λ a) ≫
      (moduleUnboundedDerivedDirectImageOverIso Λ jD a jC (h.w.trans (Category.id_comp jD))).hom =
      moduleUnboundedLowerShriekToDirectImage Λ jD := by
  apply refinementOuterComparison
    (moduleUnboundedProperOpenMate (𝟙 U) jC jD a h.flip Λ) _ _ _
    (moduleUnboundedDerivedDirectImageIdIso Λ U)
    (moduleUnboundedDerivedDirectImageSquareIso Λ a (𝟙 U) jD jC h.flip.w)
  · intro K
    exact (moduleUnboundedDerivedProperRefinementComparison_identitySourceMate jC jD a h Λ K).symm
  · exact moduleUnboundedDerivedDirectImageSquareIso_refinement Λ jC jD a h
  · exact moduleUnboundedProperOpenMate_toDirectImageSquare (𝟙 U) jC jD a h.flip Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
