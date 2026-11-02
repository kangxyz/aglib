/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.AsSubring


/-!
# Nonemptiness of the original unit-locus scheme

The canonical localization map to the same fraction field supplies a point
of the original principal-open spectrum. No alternate open scheme is chosen.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

universe u vK

namespace AlgebraicGeometry.Scheme

/-- The original principal-open spectrum has an actual point over the same fraction field. -/
theorem awaySpec_nonempty (R : Type u) (K : Type vK) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (x : R) (hx : x ≠ 0) :
    Nonempty (Spec (.of (Localization.Away x))) := by
  let hU : Submonoid.powers x ≤ R⁰ :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
  let q := Localization.mapToFractionRing K (Submonoid.powers x) (Localization.Away x) hU
  exact ⟨PrimeSpectrum.comap q.toRingHom (genericPoint (Spec (.of K)))⟩

end AlgebraicGeometry.Scheme
