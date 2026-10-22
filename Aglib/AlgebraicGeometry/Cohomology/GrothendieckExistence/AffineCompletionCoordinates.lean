/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCompletionSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineGeneratedIdeal

/-! # Completion sections in a specified original affine ideal

Transport the comparison and original-unit equation together before
specializing a generated ideal. No alternate completion model is introduced.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable (B : CommRingCat.{u}) [IsNoetherianRing B]
  (K : (Spec B).IdealSheafData) (H : (Spec B).CoherentSheaf)

/-- Whole original-unit comparison transported along an independent ideal equality. -/
def affineCompletionCoordinates (J : Ideal B) (hJ : affineIdeal B K = J) :
    { e : AdicCompletion J (moduleSpecΓFunctor.obj H.obj) ≃ₗ[B]
        ((completionFunctor (Spec B) K).obj H).affineFormalSections //
      ∀ x n, (e (AdicCompletion.of J _ x)).val (op n) = affineCompletionUnit B K H n x } := by
  subst J
  let F := (completionFunctor (Spec B) K).obj H
  let := F.affineFormalSectionsModule
  let := F.affineSections_isCompatibleSystem.sectionsScalarTower
  exact ⟨(affineCompletionSectionsEquiv B K H).restrictScalars B,
    affineCompletionSectionsEquiv_of B K H⟩

/-- The generated-ideal specialization retains the original ring ideal literally. -/
def generatedCompletionSectionsEquiv (J : Ideal B) :
    AdicCompletion J (moduleSpecΓFunctor.obj H.obj) ≃ₗ[B]
      AdicSystem.affineFormalSections
        ((completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj H) :=
  (affineCompletionCoordinates B (idealThickeningIdealSheaf (𝟙 (Spec B)) J) H J
    (affineIdeal_idealThickeningIdealSheaf B J)).val

/-- All original quotient units are retained after the ideal-coordinate transport. -/
theorem generatedCompletionSectionsEquiv_of (J : Ideal B)
    (x : moduleSpecΓFunctor.obj H.obj) (n : ℕ) :
    (generatedCompletionSectionsEquiv B H J (AdicCompletion.of J _ x)).val (op n) =
      affineCompletionUnit B (idealThickeningIdealSheaf (𝟙 (Spec B)) J) H n x :=
  (affineCompletionCoordinates B (idealThickeningIdealSheaf (𝟙 (Spec B)) J) H J
    (affineIdeal_idealThickeningIdealSheaf B J)).property x n

end AlgebraicGeometry.Scheme.Modules.Coherent
