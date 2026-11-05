/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict

/-! # The literal principal quotient as the complement of the original D(s) -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (R : Type u) [CommRing R] (s : R)

/-- The original principal open, without changing its scheme model. -/
abbrev principalSupportOpen : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen s

/-- The original quotient ring map, not a chosen reduced closed replacement. -/
abbrev principalSupportClosedMap :
    Spec (.of (R ⧸ Ideal.span {s})) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {s})))

/-- Exact complement equality for the actual open and closed arrows. -/
theorem principalSupport_complement :
    Set.range (principalSupportOpen R s).ι =
      (Set.range (principalSupportClosedMap R s))ᶜ := by
  rw [Scheme.Opens.range_ι]
  change (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum R)) =
    (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {s}))))ᶜ
  rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
  exact PrimeSpectrum.basicOpen_eq_zeroLocus_compl s

end AlgebraicGeometry.Scheme
