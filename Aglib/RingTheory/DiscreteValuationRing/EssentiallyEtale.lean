/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalRing.SeparatedPrincipal
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Unramified.LocalRing

/-! # Actual local essentially étale extensions of a DVR

The target domain structure is proved from the actual uniformizer and separatedness.
No domain, DVR, or residue-field comparison is assumed for the target.
-/

@[expose] public noncomputable section

namespace Algebra.FormallyUnramified

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [EssFiniteType R S]
  [Module.Flat R S] [FormallyUnramified R S]

omit [Module.Flat R S] in
/-- The image of an original uniformizer generates the actual target maximal ideal. -/
theorem maximalIdeal_eq_span_uniformizer {π : R} (hπ : Irreducible π) :
    maximalIdeal S = Ideal.span {algebraMap R S π} := by
  rw [← FormallyUnramified.map_maximalIdeal (R := R) (S := S),
    hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

omit [EssFiniteType R S] [FormallyUnramified R S] in
/-- Every power of the original uniformizer remains nonzero by actual faithful flatness. -/
theorem uniformizer_pow_ne_zero_of_flat_local {π : R} (hπ : Irreducible π) (n : ℕ) :
    (algebraMap R S π) ^ n ≠ 0 := by
  let : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← map_pow]
  intro h
  apply pow_ne_zero n hπ.ne_zero
  apply FaithfulSMul.algebraMap_injective R S
  simpa using h

include R in
/-- The actual local target is a domain; this is not a hypothesis on the extension. -/
theorem isDomain_of_flat_local_dvr : IsDomain S := by
  let : IsNoetherianRing S := EssFiniteType.isNoetherianRing R S
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact IsLocalRing.isDomain_of_isHausdorff_of_maximalIdeal_eq_span
    (algebraMap R S π) (maximalIdeal_eq_span_uniformizer R S hπ)
    (uniformizer_pow_ne_zero_of_flat_local R S hπ)

/-- A local essentially finite-type flat unramified extension is a DVR. -/
theorem isDiscreteValuationRing_of_flat_local_dvr :
    let : IsDomain S := isDomain_of_flat_local_dvr R S
    IsDiscreteValuationRing S := by
  let : IsNoetherianRing S := EssFiniteType.isNoetherianRing R S
  let : IsDomain S := isDomain_of_flat_local_dvr R S
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact IsLocalRing.isDiscreteValuationRing_of_isHausdorff_of_maximalIdeal_eq_span
    (algebraMap R S π) (maximalIdeal_eq_span_uniformizer R S hπ)
    (uniformizer_pow_ne_zero_of_flat_local R S hπ)

/-- Every original uniformizer remains irreducible in the actual local target. -/
theorem irreducible_algebraMap_of_flat_local_dvr {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R S π) := by
  let : IsDomain S := isDomain_of_flat_local_dvr R S
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (by simpa using uniformizer_pow_ne_zero_of_flat_local R S hπ 1)
    (maximalIdeal_eq_span_uniformizer R S hπ)

end Algebra.FormallyUnramified
