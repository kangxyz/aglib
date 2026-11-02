/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Finite original residue maps at closed source points

For an arbitrary locally finite-type scheme morphism, a globally closed
source point has finite extension of the original image residue field.
The proof uses the original residue-spectrum factorization.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Finiteness of the actual residue-field map at an actual closed source
point of a locally finite-type morphism. -/
theorem residueFieldMap_finite_of_closedPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) : (f.residueFieldMap x).hom.Finite := by
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have : LocallyOfFiniteType
      (Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x)) := by
    rw [f.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  let : LocallyOfFiniteType (Spec.map (f.residueFieldMap x)) :=
    locallyOfFiniteType_of_comp (Spec.map (f.residueFieldMap x)) (Y.fromSpecResidueField (f x))
  have hft : (f.residueFieldMap x).hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  exact RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hft

end AlgebraicGeometry.Scheme.Hom
