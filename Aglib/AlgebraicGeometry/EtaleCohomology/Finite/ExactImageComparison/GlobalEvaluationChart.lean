/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GlobalEvaluationTuple
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.ChartEvaluationCoordinate
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.TupleCoordinateTransport

/-! # Global finite evaluation tuples from actual affine chart mates -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

open CoefficientStalkBaseChange
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
  (R Ω : Type u) [CommRing R] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
  (g : Spec (.of R) ⟶ S) [Etale g]
  (s : Spec (.of Ω) ⟶ S) (hs : Spec.algebraMap R Ω ≫ g = s)

include hs

/-- An actual affine chart identifies the original finite evaluation tuple.
The chart comparison is the canonical étale mate, not an abstract chart iso. -/
theorem finiteDirectImageEvaluationTuple_isIso_of_chart
    (F : AbelianSheaf.{u, u + 1} X) : IsIso (directImageEvaluationTuple f s F) := by
  apply isIso_of_tuple_coordinates_via_iso
    (directImageChartStalkIso f g (Spec.algebraMap R Ω) s hs F)
    (finiteAffineExtendedStalkIso R Ω (pullback.fst g f)
      ((inverseImage (pullback.snd g f)).obj F))
    (Iso.refl _) (finiteChartEvaluationIndex f R Ω g s hs).symm
    (finiteChartPointStalkIso f R Ω g s hs F) (directImageEvaluationTuple f s F)
  intro z x
  exact finiteChartEvaluation_coordinate f R Ω g s hs F x z

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
