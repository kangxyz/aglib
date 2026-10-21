/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedGeometry
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedTensorNaturality
public import Aglib.AlgebraicGeometry.AffineScheme.BaseChangeChartNaturality

/-! # Actual restriction morphisms of formal graded tensor charts -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (U V : X.affineOpens) (h : V.val ≤ U.val)

/-- The tensor-coordinate restriction uses the original restriction on the
first factor and the identity on the external associated-graded factor. -/
def formalGradedChartRestriction :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    Spec (CommRingCat.of (Γ(X, V) ⊗[A] I.associatedGraded)) ⟶
      Spec (CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded)) := by
  letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  exact Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom)

@[reassoc (attr := simp)]
theorem formalGradedChartRestriction_chart :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    formalGradedChartRestriction f I U V h ≫ formalGradedChart f I U =
      formalGradedChart f I V := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  exact AffineBaseChange.tensorChartMap_naturality (A := A) (B := Γ(X, U))
    (C := I.associatedGraded) (D := Γ(X, V)) f U.property.fromSpec V.property.fromSpec
    (formalGradedChart_over f U) (formalGradedChart_over f V)
    (formalGradedCoordinateRestriction f h)
    (U.property.map_fromSpec V.property (homOfLE h).op)

instance formalGradedChartRestriction_isOpenImmersion :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    IsOpenImmersion (formalGradedChartRestriction f I U V h) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  have : IsOpenImmersion
      (formalGradedChartRestriction f I U V h ≫ formalGradedChart f I U) := by
    rw [formalGradedChartRestriction_chart]
    infer_instance
  exact IsOpenImmersion.of_comp _ (formalGradedChart f I U)

end AlgebraicGeometry.Scheme.Cohomology
