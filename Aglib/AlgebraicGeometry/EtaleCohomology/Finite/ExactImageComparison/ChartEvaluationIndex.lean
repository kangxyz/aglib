/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.AffineComponentGeometricIndex

/-! # Actual finite affine chart components indexed by the original geometric fibre -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
  (R Ω : Type u) [CommRing R] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
  (g : Spec (.of R) ⟶ S)
  (s : Spec (.of Ω) ⟶ S) (hs : Spec.algebraMap R Ω ≫ g = s)

/-- The literal chart component index maps to the original geometric fibre. -/
def finiteChartEvaluationIndex :
    MaximalSpectrum Γ(finiteAffineSource R Ω (pullback.fst g f), ⊤) ≃
      {x : Spec (.of Ω) ⟶ X // x ≫ f = s} :=
  (finiteAffineComponentGeometricIndex R Ω (pullback.fst g f)).trans
    ((pullbackPointOverEquiv g f (Spec.algebraMap R Ω)).trans
      (pointOverEquivOfBaseEq f hs))

/-- The inverse index retains the original point, not just its support. -/
theorem finiteChartEvaluationIndex_symm_point
    (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = s}) :
    finiteAffineExtendedPoint R Ω (pullback.fst g f)
        ((finiteChartEvaluationIndex f R Ω g s hs).symm x) ≫ pullback.snd g f = x.val := by
  have he := congrArg Subtype.val ((finiteChartEvaluationIndex f R Ω g s hs).apply_symm_apply x)
  change (finiteAffineComponentGeometricIndex R Ω (pullback.fst g f)
    ((finiteChartEvaluationIndex f R Ω g s hs).symm x)).val ≫ pullback.snd g f = x.val at he
  rw [finiteAffineComponentGeometricIndex_apply] at he
  exact he

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
