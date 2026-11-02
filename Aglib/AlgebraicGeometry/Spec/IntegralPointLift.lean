/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Original points lifted through an integral affine map

Lying over lifts a specified point along an injective integral original map.
Its image in an integral local base extension is the actual closed point,
proved from the original contractions. No residue-field embedding is asserted.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Spec

universe u

/-- Lift the specified original point, retaining both its original image and
its closed-point image on the integral local base extension. -/
theorem exists_point_lift_over_closedPoint
    (R T C B : Type u) [CommRing R] [IsLocalRing R]
    [CommRing T] [IsLocalRing T] [CommRing C] [CommRing B]
    [Algebra R T] [Algebra.IsIntegral R T]
    [Algebra R C] [Algebra R B] [Algebra T B] [IsScalarTower R T B]
    (φ : C →ₐ[R] B) (hφ : φ.toRingHom.IsIntegral) (hinj : Function.Injective φ)
    (x : Spec (.of C)) (hx : Spec.algebraMap R C x = IsLocalRing.closedPoint R) :
    ∃ y : Spec (.of B), Spec.map (CommRingCat.ofHom φ.toRingHom) y = x ∧
      Spec.algebraMap T B y = IsLocalRing.closedPoint T := by
  obtain ⟨y, hy⟩ := hφ.comap_surjective hinj x
  have hbase : PrimeSpectrum.comap (algebraMap R T)
      (PrimeSpectrum.comap (algebraMap T B) y) = IsLocalRing.closedPoint R := by
    calc
      _ = PrimeSpectrum.comap (algebraMap R B) y := by
        rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq R T B]
      _ = PrimeSpectrum.comap (algebraMap R C) (PrimeSpectrum.comap φ.toRingHom y) := by
        rw [← PrimeSpectrum.comap_comp_apply]
        exact congrArg (fun g : R →+* B => PrimeSpectrum.comap g y) φ.comp_algebraMap.symm
      _ = IsLocalRing.closedPoint R := by rw [hy]; exact hx
  have hmax : (PrimeSpectrum.comap (algebraMap T B) y).asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) _ (by
      change (PrimeSpectrum.comap (algebraMap R T)
        (PrimeSpectrum.comap (algebraMap T B) y)).asIdeal.IsMaximal
      rw [hbase]
      exact IsLocalRing.maximalIdeal.isMaximal R)
  refine ⟨y, hy, ?_⟩
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

end AlgebraicGeometry.Spec
