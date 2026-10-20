/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph

/-!
# A joint finite model of an integral proper curve and the two-chart line

The source construction is `exists_finite_birational_H1_model` in
`AlgebraicGeometry.Scheme.OverField.Curve.Cohomology.ProperCurveFiniteness`, lines
1244-1269 at R5 revision `5b493a5709ba2e4242f94cf163611602c03f3cf3`.
That proof constructs both finite graph projections before its H1 calculation.
This export retains those actual maps without a cohomological premise or call.
The model is integral and is unchanged over a nonempty affine open of the
original curve. No normality, smoothness or perfectness is assumed here.
-/




@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart
open AlgebraicGeometry.Scheme

open CategoryTheory AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
open _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart (projection twoChartLine)
open AlgebraicGeometry.Scheme.OverField.Curve.Projectivity

namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity

universe u

variable {K : Type u} [Field K]

/-- The same integral graph model has finite dominant maps to the original
proper curve and to the actual two-chart projective line. -/
theorem exists_finite_birational_twoChartLine_model (X : FScheme K)
    [IsIntegral X.left] [IsNoetherian X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1) :
    ∃ (Y : FScheme K) (p : Y ⟶ X)
      (q : Y ⟶ Over.mk (projection (.of K))),
      IsIntegral Y.left ∧ IsFinite p.left ∧ IsDominant p.left ∧
      IsFinite q.left ∧ IsDominant q.left ∧
      ∃ U : X.left.affineOpens, Nonempty U.1 ∧ IsIso (p.left ∣_ U.1) := by
  obtain ⟨U, hU, a, ha⟩ := GraphInput.exists_affine_transcendental X hdim
  let : Nonempty U.1 := hU
  let P : FScheme K := Over.mk (projection (.of K))
  let : IsProper P.hom := inferInstanceAs (IsProper (projection (.of K)))
  let : IsIntegral P.left := inferInstanceAs (IsIntegral (twoChartLine (.of K)))
  let r := affineSectionToLine X U a
  let hr := affineSectionToLine_over X U a
  let : IsDominant r := affineSectionToLine_isDominant X U a ha
  let Y := rationalGraphImage X P U.1 r hr
  let p := rationalGraphProjectionLeft X P U.1 r hr
  let q := rationalGraphProjectionRight X P U.1 r hr
  have hYdim : topologicalKrullDim Y.left ≤ 1 :=
    rationalGraphImage_dimension_le_one X hdim.le U.1 r hr
  let : IsFinite p.left := proper_dominant_curve_isFinite p.left hYdim hdim
  let : IsFinite q.left := proper_dominant_curve_isFinite q.left hYdim
    (twoChartLine_topologicalKrullDim K)
  exact ⟨Y, p, q, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, U, hU, inferInstance⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
