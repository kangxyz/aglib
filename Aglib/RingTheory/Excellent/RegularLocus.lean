/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.GeometricConditions
public import Aglib.RingTheory.DiscreteValuationRing.DimensionOne
public import Aglib.RingTheory.RegularLocalRing.PrimeLocalization
public import Aglib.RingTheory.RegularLocalRing.Localization
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Regular open subsets and semilocal normal surfaces

Regularity is tested on the actual prime localizations in
`PrimeSpectrum.regularLocus`. A normal Noetherian domain of dimension at most
two is regular at every nonmaximal prime. When its maximal spectrum is finite,
the singular locus is therefore finite and closed, and its regular locus is
nonempty and open.

The J-0 interface records a nonempty regular open subset. For domains it is
equivalent to regularity of a localization away from one nonzero element.
These statements supply the finite normal models in the J-2 criterion;
they do not themselves assert that every finite-type algebra has open regular
locus.
-/

@[expose] public noncomputable section

universe u v

open IsLocalRing

/-- A Noetherian ring is J-0 when its regular locus contains a nonempty open set. -/
def IsJ0Ring (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ ∃ U : Set (PrimeSpectrum R),
    IsOpen U ∧ U.Nonempty ∧ U ⊆ PrimeSpectrum.regularLocus R

namespace PrimeSpectrum

/-- Regularity of a prime localization passes to every smaller prime. -/
theorem mem_regularLocus_of_le {R : Type u} [CommRing R]
    {p q : PrimeSpectrum R} (hpq : p ≤ q) (hq : q ∈ regularLocus R) :
    p ∈ regularLocus R := by
  let S := Localization.AtPrime q.asIdeal
  let P := p.asIdeal.map (algebraMap R S)
  let : IsRegularLocalRing S := hq
  let : P.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime q.asIdeal hpq
  let T := Localization.AtPrime P
  let : IsRegularLocalRing T := IsRegularLocalRing.atPrime S P
  have hP : P.comap (algebraMap R S) = p.asIdeal :=
    Ideal.under_map_of_isLocalizationAtPrime q.asIdeal hpq
  let : IsLocalization.AtPrime T p.asIdeal := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      q.asIdeal.primeCompl T P using 1
    exact hP.symm
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.asIdeal.primeCompl T
      (Localization.AtPrime p.asIdeal)).toRingEquiv

/-- The regular locus is stable under generalization, without an openness premise. -/
theorem regularLocus_stableUnderGeneralization (R : Type u) [CommRing R] :
    StableUnderGeneralization (regularLocus R) := by
  intro q p hpq hq
  exact mem_regularLocus_of_le ((le_iff_specializes p q).mpr hpq) hq

/-- The generic point of a domain is regular. -/
theorem bot_mem_regularLocus (R : Type u) [CommRing R] [IsDomain R] :
    (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ∈ regularLocus R := by
  let : Field (Localization.AtPrime (⊥ : Ideal R)) := IsField.toField <| by
    simp [isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
  exact inferInstanceAs (IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal R)))

/-- A domain has a regular point even when its regular locus is not known to be open. -/
theorem regularLocus_nonempty (R : Type u) [CommRing R] [IsDomain R] :
    (regularLocus R).Nonempty :=
  ⟨⟨⊥, inferInstance⟩, bot_mem_regularLocus R⟩

/-- Regularity throughout a basic open gives regularity of its actual away localization. -/
theorem isRegularRing_away_of_basicOpen_subset
    {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R)
    (h : (basicOpen f : Set (PrimeSpectrum R)) ⊆ regularLocus R) :
    IsRegularRing (Localization.Away f) := by
  let S := Localization.Away f
  apply isRegularRing_iff.mpr
  intro q hq
  let p := q.comap (algebraMap R S)
  have hfp : f ∉ p := by
    intro hf
    exact hq.ne_top (q.eq_top_of_isUnit_mem hf (IsLocalization.Away.algebraMap_isUnit f))
  let : IsRegularLocalRing (Localization.AtPrime p) := @h ⟨p, inferInstance⟩ hfp
  let T := Localization.AtPrime q
  let : IsLocalization.AtPrime T p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers f) T q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) T).toRingEquiv

/-- A basic open is regular exactly when its away localization is a regular ring. -/
theorem basicOpen_subset_regularLocus_iff
    {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R) :
    (basicOpen f : Set (PrimeSpectrum R)) ⊆ regularLocus R ↔
      IsRegularRing (Localization.Away f) := by
  refine ⟨isRegularRing_away_of_basicOpen_subset f, fun h p hp => ?_⟩
  let := h
  exact IsRegularRing.regular_atPrime_of_away R f p.asIdeal hp

/-- A nonmaximal prime in dimension at most two has height at most one. -/
theorem height_le_one_of_not_isMaximal
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R ≤ 2) (p : PrimeSpectrum R) (hp : ¬ p.asIdeal.IsMaximal) :
    p.asIdeal.height ≤ 1 := by
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let : m.IsMaximal := hm
  have hlt : p.asIdeal < m := lt_of_le_of_ne hpm (fun he => hp (he.symm ▸ hm))
  have hm2 : m.height ≤ (2 : ℕ∞) := by
    exact WithBot.coe_le_coe.mp (m.height_le_ringKrullDim_of_isPrime.trans hdim)
  have hbound := (Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans hm2
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (p.asIdeal.height_ne_top p.isPrime.ne_top)
  rw [← hn] at hbound ⊢
  have hn2 : n + 1 ≤ 2 := by exact_mod_cast hbound
  exact_mod_cast (show n ≤ 1 by omega)

/-- A normal Noetherian domain of dimension at most two is regular at nonmaximal primes. -/
theorem mem_regularLocus_of_not_isMaximal
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R ≤ 2) (p : PrimeSpectrum R) (hp : ¬ p.asIdeal.IsMaximal) :
    p ∈ regularLocus R := by
  let S := Localization.AtPrime p.asIdeal
  let : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization
    S p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors
  have hdimS : ringKrullDim S ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal S]
    exact_mod_cast height_le_one_of_not_isMaximal hdim p hp
  by_cases hf : IsField S
  · let := hf.toField
    exact inferInstanceAs (IsRegularLocalRing S)
  · let : IsDiscreteValuationRing S :=
      IsDiscreteValuationRing.of_isIntegrallyClosed_of_dimLE_one S hdimS hf
    exact inferInstanceAs (IsRegularLocalRing S)

/-- The singular locus of a semilocal normal Noetherian surface is finite. -/
theorem finite_compl_regularLocus_of_isIntegrallyClosed_of_dimLE_two
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Finite (MaximalSpectrum R)] (hdim : ringKrullDim R ≤ 2) :
    ((regularLocus R)ᶜ).Finite := by
  apply (Set.finite_range (MaximalSpectrum.toPrimeSpectrum (R := R))).subset
  intro p hp
  have hm : p.asIdeal.IsMaximal := by
    by_contra h
    exact hp (mem_regularLocus_of_not_isMaximal hdim p h)
  exact ⟨⟨p.asIdeal, hm⟩, PrimeSpectrum.ext rfl⟩

/-- The regular locus of a semilocal normal Noetherian surface is open. -/
theorem isOpen_regularLocus_of_isIntegrallyClosed_of_dimLE_two
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Finite (MaximalSpectrum R)] (hdim : ringKrullDim R ≤ 2) :
    IsOpen (regularLocus R) := by
  apply isClosed_compl_iff.mp
  have hs := finite_compl_regularLocus_of_isIntegrallyClosed_of_dimLE_two R hdim
  have he : (⋃ p ∈ (regularLocus R)ᶜ, ({p} : Set (PrimeSpectrum R))) =
      (regularLocus R)ᶜ := by
    ext p
    simp
  rw [← he]
  apply hs.isClosed_biUnion
  intro p hp
  apply (isClosed_singleton_iff_isMaximal p).mpr
  by_contra h
  exact hp (mem_regularLocus_of_not_isMaximal hdim p h)

end PrimeSpectrum

namespace IsJ0Ring

/-- The principal-open form of J-0 for a domain, used in generic descent and ascent. -/
theorem iff_exists_regular_away
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    IsJ0Ring R ↔ ∃ f : R, f ≠ 0 ∧ IsRegularRing (Localization.Away f) := by
  constructor
  · rintro ⟨_, U, hU, ⟨p, hp⟩, hreg⟩
    obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hU p hp
    refine ⟨f, ?_, PrimeSpectrum.isRegularRing_away_of_basicOpen_subset f (hfU.trans hreg)⟩
    intro hf
    exact hpf (hf ▸ p.asIdeal.zero_mem)
  · rintro ⟨f, hf, hreg⟩
    refine ⟨inferInstance, PrimeSpectrum.basicOpen f,
      (PrimeSpectrum.basicOpen f).isOpen, ?_, ?_⟩
    · refine ⟨⟨⊥, inferInstance⟩, ?_⟩
      change f ∉ (⊥ : Ideal R)
      simpa only [Ideal.mem_bot] using hf
    · exact (PrimeSpectrum.basicOpen_subset_regularLocus_iff f).mpr hreg

/-- A semilocal normal Noetherian domain of dimension at most two is J-0. -/
theorem of_isIntegrallyClosed_of_dimLE_two
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Finite (MaximalSpectrum R)] (hdim : ringKrullDim R ≤ 2) : IsJ0Ring R :=
  ⟨inferInstance, PrimeSpectrum.regularLocus R,
    PrimeSpectrum.isOpen_regularLocus_of_isIntegrallyClosed_of_dimLE_two R hdim,
    PrimeSpectrum.regularLocus_nonempty R, Set.Subset.rfl⟩

end IsJ0Ring

namespace Module.Finite

/-- A finite algebra over a semilocal ring is semilocal, using its actual residue fibres. -/
theorem maximalSpectrum_finite_of_finite_base
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Finite (MaximalSpectrum R)] : Finite (MaximalSpectrum S) := by
  have (p : MaximalSpectrum R) : IsArtinianRing (p.asIdeal.Fiber S) :=
    IsArtinianRing.of_finite p.asIdeal.ResidueField _
  have (p : MaximalSpectrum R) : Finite (p.asIdeal.primesOver S) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R S p.asIdeal).finite_iff.mpr inferInstance
  let f : MaximalSpectrum S → Σ p : MaximalSpectrum R, p.asIdeal.primesOver S :=
    fun q => ⟨⟨q.asIdeal.under R, Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal⟩,
      q.asIdeal, q.isMaximal.isPrime, ⟨rfl⟩⟩
  apply _root_.Finite.of_injective f
  intro p q hpq
  exact MaximalSpectrum.ext
    (congrArg (fun x : Σ p : MaximalSpectrum R, p.asIdeal.primesOver S => x.2.1) hpq)

end Module.Finite
