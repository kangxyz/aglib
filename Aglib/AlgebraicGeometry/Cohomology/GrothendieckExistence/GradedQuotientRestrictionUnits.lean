/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalQuotientUnitProperty
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAmbientRestrictionSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinateRestrictionPresentation

/-! # Original degree-zero images after chart restriction -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct DirectSum
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))
  (U V : X.affineOpens) (h : V.val ≤ U.val)

/-- The smaller quotient sends the original restricted ambient unit to the
original degree-zero section inclusion. -/
theorem formalGradedLocalSectionQuotient_restricted_unit
    (m : Γ(F.gradedPiece 0, U)) :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
    letI : IsOpenImmersion (Spec.map φ) :=
      formalGradedChartRestriction_isOpenImmersion f I U V h
    chartPullbackCoordinatesRestrictionPostcomposeEquation
      (formalGradedProjection f I) U.property.fromSpec
      (formalGradedChart f I U) (formalGradedChart f I V) φ
      (formalGradedChartRestriction_chart f I U V h)
      (formalGradedChart_projection f I U) (F.gradedPiece 0)
      (affineChartΓIso U (F.gradedPiece 0))
      (fun x => formalGradedLocalSectionQuotient f I F V x)
      (fun y => DirectSum.of (fun n => Γ(F.gradedPiece n, V)) 0
        ((F.gradedPiece 0).val.map (homOfLE h).op y)) m := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  let : IsOpenImmersion (Spec.map φ) :=
    formalGradedChartRestriction_isOpenImmersion f I U V h
  exact chartPullbackCoordinatesRestrictionPostcomposeEquation_of_presentation_unit
    (formalGradedProjection f I) U.property.fromSpec
    (formalGradedChart f I U) (formalGradedChart f I V) φ
    (formalGradedChartRestriction_chart f I U V h)
    (formalGradedChart_projection f I U) (F.gradedPiece 0)
    (affineChartΓIso U (F.gradedPiece 0))
    (formalGradedLocalSectionQuotient f I F V)
    (fun y => DirectSum.of (fun n => Γ(F.gradedPiece n, V)) 0
      ((F.gradedPiece 0).val.map (homOfLE h).op y)) m
    V.property.fromSpec (formalGradedChart_projection f I V)
    (affineChartΓIso V (F.gradedPiece 0))
    (fun y => (F.gradedPiece 0).val.map (homOfLE h).op y)
    (formalGradedAmbientSectionRestriction_one_tmul f I F U V h m)
    (formalGradedLocalSectionQuotient_unit_property f I F V
      ((F.gradedPiece 0).val.map (homOfLE h).op m))

end AlgebraicGeometry.Scheme.Cohomology
