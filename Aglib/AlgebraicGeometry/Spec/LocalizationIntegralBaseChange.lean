/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.IntegralBaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Integral and normal base changes along the original localization map

The actual localization spectrum contains the original generic point. The
flat-preimmersion theorem therefore applies directly to its literal map,
without introducing a second stalk-ring realization. Normality uses the same
projection stalk isomorphisms and does not need a generic-point hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]

/-- The original generic point lies in the actual localization image when
no denominator is a zero divisor. -/
theorem genericPoint_mem_range_localization [IsDomain R]
    (hM : M ≤ nonZeroDivisors R) :
    genericPoint (Spec (.of R)) ∈ Set.range (Spec.algebraMap R S) := by
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  let : IsDominant (Spec.algebraMap R S) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap R S))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsLocalization.injective S hM)]
    exact bot_le
  exact ⟨genericPoint (Spec (.of S)), map_genericPoint_of_isDominant _ (Spec.algebraMap R S)⟩

/-- The literal localization pullback of an integral dominant scheme is
integral; the generic image condition is derived internally. -/
theorem isIntegral_pullback_localization [IsDomain R]
    (hM : M ≤ nonZeroDivisors R) {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (.of R)) [IsDominant p] :
    IsIntegral (pullback p (Spec.algebraMap R S)) := by
  let : Flat (Spec.algebraMap R S) := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S M))
  let : IsPreimmersion (Spec.algebraMap R S) := IsPreimmersion.of_isLocalization M
  exact isIntegral_pullback_of_flat_preimmersion p (Spec.algebraMap R S)
    (genericPoint_mem_range_localization R S M hM)

include M in
/-- Normality is retained on the unchanged pullback by the literal original
localization map, without a domain or finite-presentation assumption. -/
theorem normalStalks_pullback_localization {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of R)) (hY : NormalStalks Y) :
    NormalStalks (pullback p (Spec.algebraMap R S)) := by
  let : Flat (Spec.algebraMap R S) := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S M))
  let : IsPreimmersion (Spec.algebraMap R S) := IsPreimmersion.of_isLocalization M
  exact normalStalks_pullback_of_flat_preimmersion p (Spec.algebraMap R S) hY

end AlgebraicGeometry.Scheme
