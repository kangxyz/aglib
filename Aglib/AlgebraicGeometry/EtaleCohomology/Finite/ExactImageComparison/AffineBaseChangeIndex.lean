/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.AffineComponentGeometricIndex
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.CartesianPointOverEquiv

/-! # Matching actual finite component indices across affine base change -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R R' Ω : Type u) [CommRing R] [CommRing R'] [Field Ω] [IsAlgClosed Ω]
  [Algebra R Ω] [Algebra R' Ω]
  {X X' : Scheme.{u}} (f : X ⟶ Spec (.of R)) (f' : X' ⟶ Spec (.of R'))
  [IsFinite f] [IsFinite f'] (g : Spec (.of R') ⟶ Spec (.of R)) (g' : X' ⟶ X)
  (h : IsPullback g' f' f g)
  (hpoint : Spec.algebraMap R' Ω ≫ g = Spec.algebraMap R Ω)

/-- The two actual maximal-component indices are matched through the same
original geometric fibre, using the specified cartesian square. -/
def finiteAffineBaseChangeIndex :
    MaximalSpectrum Γ(finiteAffineSource R' Ω f', ⊤) ≃
      MaximalSpectrum Γ(finiteAffineSource R Ω f, ⊤) :=
  (finiteAffineComponentGeometricIndex R' Ω f').trans
    ((cartesianPointOverEquiv g' f' f g h (Spec.algebraMap R' Ω)).trans
      ((pointOverEquivOfBaseEq f hpoint).trans
        (finiteAffineComponentGeometricIndex R Ω f).symm))

/-- The index matching preserves the actual original geometric points, not just
component supports or chosen residue-field isomorphism classes. -/
theorem finiteAffineBaseChangeIndex_point
    (m : MaximalSpectrum Γ(finiteAffineSource R' Ω f', ⊤)) :
    finiteAffineExtendedPoint R Ω f
        (finiteAffineBaseChangeIndex R R' Ω f f' g g' h hpoint m) =
      finiteAffineExtendedPoint R' Ω f' m ≫ g' := by
  have hh := congrArg Subtype.val
    ((finiteAffineComponentGeometricIndex R Ω f).apply_symm_apply
      ((pointOverEquivOfBaseEq f hpoint)
        ((cartesianPointOverEquiv g' f' f g h (Spec.algebraMap R' Ω))
          (finiteAffineComponentGeometricIndex R' Ω f' m))))
  change (finiteAffineComponentGeometricIndex R Ω f
      (finiteAffineBaseChangeIndex R R' Ω f f' g g' h hpoint m)).val =
    (finiteAffineComponentGeometricIndex R' Ω f' m).val ≫ g' at hh
  rw [finiteAffineComponentGeometricIndex_apply, finiteAffineComponentGeometricIndex_apply] at hh
  exact hh

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
