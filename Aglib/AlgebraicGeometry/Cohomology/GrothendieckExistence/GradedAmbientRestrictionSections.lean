/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAmbientRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinateRestriction

/-! # Ambient unit tensors retain original affine restriction maps -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))
  (U V : X.affineOpens) (h : V.val ≤ U.val)

/-- Actual affine sections of the restriction unit followed by native chart rebracketing. -/
def formalGradedAmbientSectionRestriction :=
  letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  letI : IsOpenImmersion (Spec.map φ) :=
    formalGradedChartRestriction_isOpenImmersion f I U V h
  affineChartSectionRestriction φ (formalGradedChart f I U) (formalGradedChart f I V)
    (formalGradedChartRestriction_chart f I U V h)
    ((Scheme.Modules.pullback (formalGradedProjection f I)).obj (F.gradedPiece 0))

/-- The actual ambient restriction preserves the original coordinate unit sections.
The shared predicate unfolds to the original one-tensor restriction equation. -/
theorem formalGradedAmbientSectionRestriction_one_tmul (m : Γ(F.gradedPiece 0, U)) :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
    letI : IsOpenImmersion (Spec.map φ) :=
      formalGradedChartRestriction_isOpenImmersion f I U V h
    chartPullbackCoordinatesRestrictionEquation (formalGradedProjection f I) U V h
      (formalGradedChart f I U) (formalGradedChart f I V) φ
      (formalGradedChartRestriction_chart f I U V h)
      (formalGradedChart_projection f I U) (formalGradedChart_projection f I V)
      (F.gradedPiece 0) m := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  let : IsOpenImmersion (Spec.map φ) :=
    formalGradedChartRestriction_isOpenImmersion f I U V h
  exact chartPullbackCoordinatesRestrictionEquation_of_coordinates
    (formalGradedProjection f I) U V h
    (formalGradedChart f I U) (formalGradedChart f I V) φ
    (formalGradedChartRestriction_chart f I U V h)
    (formalGradedChart_projection f I U) (formalGradedChart_projection f I V)
    (F.gradedPiece 0) m

end AlgebraicGeometry.Scheme.Cohomology
