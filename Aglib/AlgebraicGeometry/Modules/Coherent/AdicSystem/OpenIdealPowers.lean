/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Arbitrary ideal powers under open restriction

This applies to the independent exceptional ideal, not only ideals induced
from an affine base. It concerns finite-order restriction, not localization
of completed modules.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.IdealSheafData
universe u

private theorem comap_pow_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (J : Ideal R) (n : ℕ) :
    (J ^ n).comap e.symm = (J.comap e.symm) ^ n := by
  rw [Ideal.comap_symm, Ideal.comap_symm, Ideal.map_pow]

/-- Open restriction preserves every power of an arbitrary ideal sheaf. -/
theorem comap_pow_of_isOpenImmersion {X Y : Scheme.{u}} (p : Y ⟶ X)
    [IsOpenImmersion p] (K : X.IdealSheafData) (n : ℕ) :
    (K ^ n).comap p = K.comap p ^ n := by
  apply IdealSheafData.ext
  funext U
  simp only [ideal_comap_of_isOpenImmersion, ideal_pow, Pi.pow_apply]
  exact comap_pow_ringEquiv (p.appIso U).commRingCatIsoToRingEquiv _ n

end AlgebraicGeometry.Scheme.IdealSheafData
