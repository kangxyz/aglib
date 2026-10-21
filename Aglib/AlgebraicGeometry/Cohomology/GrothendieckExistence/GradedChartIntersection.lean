/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedChartRestriction
public import Aglib.AlgebraicGeometry.Limits.OpenImmersionIntersection
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Tensor charts on actual affine intersections -/

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
  (U V W : X.affineOpens) (hWU : W.val ≤ U.val) (hWV : W.val ≤ V.val)
  (hW : W.val = U.val ⊓ V.val)

include hW in
/-- The tensor chart of the actual affine intersection is the original
pullback overlap of tensor charts. No associated-graded base-change iso is used. -/
theorem formalGradedChartIntersection_isPullback :
    letI (O : X.Opens) : Algebra A Γ(X, O) := formalGradedSectionAlgebra f O
    IsPullback (formalGradedChartRestriction f I U W hWU)
      (formalGradedChartRestriction f I V W hWV)
      (formalGradedChart f I U) (formalGradedChart f I V) := by
  let (O : X.Opens) : Algebra A Γ(X, O) := formalGradedSectionAlgebra f O
  apply isPullback_of_openImmersion_range_inter (formalGradedChart f I W)
    _ _ _ _ (formalGradedChartRestriction_chart f I U W hWU)
    (formalGradedChartRestriction_chart f I V W hWV)
  rw [formalGradedChart_range, formalGradedChart_range, formalGradedChart_range,
    W.property.range_fromSpec, U.property.range_fromSpec, V.property.range_fromSpec, hW]
  rfl

include hW in
/-- The actual affine-intersection chart identifies with the categorical overlap. -/
def formalGradedChartIntersectionIso :
    letI (O : X.Opens) : Algebra A Γ(X, O) := formalGradedSectionAlgebra f O
    Spec (CommRingCat.of (Γ(X, W) ⊗[A] I.associatedGraded)) ≅
      pullback (formalGradedChart f I U) (formalGradedChart f I V) := by
  letI (O : X.Opens) : Algebra A Γ(X, O) := formalGradedSectionAlgebra f O
  exact (formalGradedChartIntersection_isPullback f I U V W hWU hWV hW).isoPullback

end AlgebraicGeometry.Scheme.Cohomology
