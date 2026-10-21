/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalQuotient
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedPresentationUnit
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.PresentationUnit

/-! # Native unit property of original local graded quotients -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct DirectSum ChangeOfRings
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))
  (U : X.affineOpens)

/-- The original quotient unit equation, retaining the native chart-coordinate head. -/
theorem formalGradedLocalSectionQuotient_unit_property (m : Γ(F.gradedPiece 0, U)) :
    letI := formalGradedSectionAlgebra f U
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
      formalGradedAffineModule f I F U
    ModuleCat.algebraTensorPresentationUnitEquation
      (chartPullbackCoordinatesIso (formalGradedProjection f I) U.property.fromSpec
        (formalGradedChart f I U) (formalGradedChart_projection f I U)
        (F.gradedPiece 0) (affineChartΓIso U (F.gradedPiece 0)))
      (formalGradedLocalSectionQuotient f I F U) m
      (DirectSum.of (fun n => Γ(F.gradedPiece n, U)) 0 m) := by
  let := formalGradedSectionAlgebra f U
  let : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule f I F U
  exact ModuleCat.algebraTensorPresentationUnitEquation_of_factorization
    (chartPullbackCoordinatesIso (formalGradedProjection f I) U.property.fromSpec
      (formalGradedChart f I U) (formalGradedChart_projection f I U)
      (F.gradedPiece 0) (affineChartΓIso U (F.gradedPiece 0)))
    (formalGradedLocalSectionQuotient f I F U)
    (ModuleCat.ofHom (formalGradedAffinePresentation f I F U)) rfl m
    (DirectSum.of (fun n => Γ(F.gradedPiece n, U)) 0 m)
    (formalGradedAffinePresentation_one_tmul f I F U m)

end AlgebraicGeometry.Scheme.Cohomology
