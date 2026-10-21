/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Support.FiniteLengthDetection

/-!
# Finite-length defects of maps bijective off the closed point

The canonical localized maps detect closed-point support of the kernel and
cokernel. Source and target may live in independent universes.
-/

@[expose] public section

namespace LinearMap

variable {R M N : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A finite source and punctured injectivity give a finite-length kernel. -/
theorem isFiniteLength_ker_of_injective_punctured [Module.Finite R M] (f : M →ₗ[R] N)
    (hf : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Function.Injective (LocalizedModule.map p.asIdeal.primeCompl f)) :
    IsFiniteLength R f.ker := by
  apply Module.isFiniteLength_of_support_subset_closedPoint
  intro p hp
  by_contra hclosed
  have hne : p.asIdeal ≠ IsLocalRing.maximalIdeal R := by
    rintro h
    exact hclosed (by rw [PrimeSpectrum.mem_zeroLocus, h])
  have hn : p ∉ Module.support R f.ker := by
    rw [Module.notMem_support_iff']
    intro m
    have hm : LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m.val = 0 := by
      apply hf p hne
      have hm0 : f m.val = 0 := m.property
      simp only [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, map_zero,
        hm0, LocalizedModule.zero_mk]
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).mp hm
    exact ⟨s, s.property, Subtype.ext hs⟩
  exact hn hp

/-- A finite target and punctured surjectivity give a finite-length cokernel. -/
theorem isFiniteLength_coker_of_surjective_punctured [Module.Finite R N] (f : M →ₗ[R] N)
    (hf : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl f)) :
    IsFiniteLength R (N ⧸ f.range) := by
  apply Module.isFiniteLength_of_support_subset_closedPoint
  intro p hp
  by_contra hclosed
  have hne : p.asIdeal ≠ IsLocalRing.maximalIdeal R := by
    rintro h
    exact hclosed (by rw [PrimeSpectrum.mem_zeroLocus, h])
  have hn : p ∉ Module.support R (N ⧸ f.range) :=
    Module.notMem_support_iff.mpr
      ((f.localizedMap_surjective_iff_subsingleton_localized_coker
        p.asIdeal.primeCompl).mp (hf p hne))
  exact hn hp

end LinearMap
