/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness of polynomial projective space over its base

The structure morphism `toSpec R ι : P_R ⟶ Spec R` is flat for every commutative ring `R` and
every coordinate type `ι` (`flat_toSpec`). Flatness is local on the source; on the standard chart
`D₊(Xᵢ)` the structure morphism is the spectrum of the coefficient map of the chart ring, which is
a polynomial ring over `R` (`coordinateRingEquivPolynomial`), hence flat
(`flat_coordinateRingCoefficient`).
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The coefficient map of a standard chart ring is flat: the chart ring is a polynomial ring
over `R` in the remaining coordinates. -/
theorem flat_coordinateRingCoefficient (i : ι) : (coordinateRingCoefficient R ι i).Flat := by
  let e := coordinateRingEquivPolynomial R ι i
  have h : e.symm.toRingHom.comp (algebraMap R (MvPolynomial {j : ι // j ≠ i} R)) =
      coordinateRingCoefficient R ι i := by
    refine RingHom.ext fun r => ?_
    change e.symm (MvPolynomial.C r) = coordinateRingCoefficient R ι i r
    rw [RingEquiv.symm_apply_eq]
    exact (coordinateRingToPolynomial_coefficient R ι i r).symm
  rw [← h]
  exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (RingHom.Flat.of_bijective e.symm.bijective)

-- Synthesizing `IsZariskiLocalAtSource @Flat` assigns `@Flat` to a `MorphismProperty` variable,
-- which unfolds `MorphismProperty` beyond instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **Projective space is flat over its base**: the structure morphism `P_R ⟶ Spec R` is flat. -/
instance flat_toSpec : Flat (toSpec R ι) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat.{u})
    (coordinateAffineOpenCover R ι).openCover
  intro i
  change Flat (Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one ≫ toSpec R ι)
  rw [coordinateChart_toSpec, HasRingHomProperty.Spec_iff (P := @Flat)]
  exact flat_coordinateRingCoefficient R ι i

end AlgebraicGeometry.ProjectiveSpace
