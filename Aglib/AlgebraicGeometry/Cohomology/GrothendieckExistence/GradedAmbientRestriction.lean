/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalQuotient
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedChartRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinateUnitProperty

/-! # Original ambient restrictions in graded tensor charts -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The actual restriction-composition comparison of the ambient coefficient. -/
def formalGradedAmbientRestrictionIso (U V : X.affineOpens) (h : V.val ≤ U.val) :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    ((formalGradedAmbient f I F).restrict (formalGradedChart f I U)).restrict
      (formalGradedChartRestriction f I U V h) ≅
        (formalGradedAmbient f I F).restrict (formalGradedChart f I V) := by
  letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  exact (restrictFunctorComp (formalGradedChartRestriction f I U V h)
      (formalGradedChart f I U)).symm.app (formalGradedAmbient f I F) ≪≫
    (restrictFunctorCongr (formalGradedChartRestriction_chart f I U V h)).app
      (formalGradedAmbient f I F)

/-- Unit tensors of original degree-zero sections are the original chart-unit sections.
The shared predicate unfolds to the equation for the actual ambient coordinate isomorphism. -/
theorem formalGradedAmbientSectionsIso_inv_one_tmul (U : X.affineOpens)
    (m : Γ(F.gradedPiece 0, U)) :
    letI := formalGradedSectionAlgebra f U
    chartPullbackCoordinateUnitEquation
      (R := Γ(X, U)) (S := Γ(X, U) ⊗[A] I.associatedGraded)
      (formalGradedProjection f I) U.property.fromSpec (formalGradedChart f I U)
      (formalGradedChart_projection f I U) (F.gradedPiece 0)
      (affineChartΓIso U (F.gradedPiece 0)) m := by
  let := formalGradedSectionAlgebra f U
  exact chartPullbackCoordinateUnitEquation_of_coordinates
    (R := Γ(X, U)) (S := Γ(X, U) ⊗[A] I.associatedGraded)
    (formalGradedProjection f I) U.property.fromSpec (formalGradedChart f I U)
    (formalGradedChart_projection f I U) (F.gradedPiece 0)
    (affineChartΓIso U (F.gradedPiece 0)) m

end AlgebraicGeometry.Scheme.Cohomology
