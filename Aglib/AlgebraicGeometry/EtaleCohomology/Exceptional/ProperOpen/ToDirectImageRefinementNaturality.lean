/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImage
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompositionCoherence
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
theorem moduleDerivedDirectImageSquareIso_refinement :
    moduleDerivedDirectImageSquareIso Λ a (𝟙 U) jD jC h.flip.w ≪≫
      Functor.isoWhiskerRight (moduleDerivedDirectImageIdIso Λ U)
        (moduleDerivedDirectImage Λ jD) ≪≫
      Functor.leftUnitor (moduleDerivedDirectImage Λ jD) =
    moduleDerivedDirectImageOverIso Λ jD a jC (h.w.trans (Category.id_comp jD)) := by
  simp only [moduleDerivedDirectImageSquareIso, Iso.trans_assoc]
  rw [moduleDerivedDirectImageCompIso_comp_id]
  simp only [moduleDerivedDirectImageOverIso, eqToIso_trans]

/-- The original Cartesian refinement unit preserves the canonical outer-adjoint comparison. -/
theorem moduleDerivedProperRefinementComparison_toDirectImage_naturality :
    moduleDerivedProperRefinementComparison jC jD a h Λ ≫
      Functor.whiskerRight (moduleDerivedLowerShriekToDirectImage Λ jC)
        (moduleDerivedDirectImage Λ a) ≫
      (moduleDerivedDirectImageOverIso Λ jD a jC (h.w.trans (Category.id_comp jD))).hom =
      moduleDerivedLowerShriekToDirectImage Λ jD := by
  apply refinementOuterComparison
    (moduleProperOpenMate Λ jD jC (𝟙 U) a h.flip) _ _ _
    (moduleDerivedDirectImageIdIso Λ U)
    (moduleDerivedDirectImageSquareIso Λ a (𝟙 U) jD jC h.flip.w)
  · intro K
    exact (moduleDerivedProperRefinementComparison_identitySourceMate jC jD a h Λ K).symm
  · exact moduleDerivedDirectImageSquareIso_refinement Λ jC jD a h
  · exact moduleProperOpenMate_toDirectImageSquare Λ jD jC (𝟙 U) a h.flip

end AlgebraicGeometry.Scheme.EtaleCohomology
