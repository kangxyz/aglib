/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.HeightOneLocalization
public import Aglib.RingTheory.LocalRing.ParameterIdeal
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Associativity
public import Aglib.RingTheory.KrullDimension.PrincipalOpen
public import Aglib.RingTheory.Localization.HeightOne
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

/-!
# Reduced principal covers in normal local dimension two

A bounded stable parameter family and finite prime avoidance construct a
nonzero reduced principal cover of every nonzero nonunit on a normal local
Noetherian surface. The original quotient, powers and divisibility are retained.
-/

@[expose] public noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- Meeting every minimal prime over the original principal ideal gives
divisibility by a positive power, with no factorization hypothesis. -/
theorem exists_pos_pow_dvd_of_mem_minimalPrimes (a c : R)
    (hc : ∀ P ∈ (Ideal.span {a}).minimalPrimes, c ∈ P) :
    ∃ r : ℕ, 0 < r ∧ a ∣ c ^ r := by
  have hrad : c ∈ (Ideal.span {a}).radical := by
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    exact hc
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  rw [_root_.pow_succ]
  exact dvd_mul_of_dvd_left (Ideal.mem_span_singleton.mp hn) c

end Ideal

namespace IsIntegrallyClosed

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

/-- Reducedness of an actual nonzero principal quotient is detected in the
original height-one localizations of a normal Noetherian domain. -/
theorem isReduced_quotient_span_singleton_of_height_one (c : R) (hc : c ≠ 0)
    (hloc : ∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
      ((Ideal.span {c}).map (algebraMap R (Localization.AtPrime P))).IsRadical) :
    IsReduced (R ⧸ Ideal.span {c}) := by
  apply (Ideal.isRadical_iff_quotient_reduced (Ideal.span {c})).mp
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr
  intro x hx
  apply Ideal.mem_span_singleton_of_mem_map_atPrime_height_one hc
  intro P hP hheight
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mp (hloc P hheight)
  simpa only [map_pow] using
    Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime P)) hx

end IsIntegrallyClosed

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsNoetherianRing R]

omit [IsDomain R] in
private theorem ne_zero_of_parameter_pair (hdim : ringKrullDim R = 2)
    (f g : R) (hfg : (Ideal.span {f} ⊔ Ideal.span {g}).radical = maximalIdeal R) :
    f ≠ 0 := by
  intro hf
  have hg : (Ideal.span {g}).radical = maximalIdeal R := by simpa [hf] using hfg
  have hm : maximalIdeal R ∈ (Ideal.span {g}).minimalPrimes := by
    rw [← (Ideal.span {g}).radical_minimalPrimes, hg,
      Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hh := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
    (Ideal.span {g}) (maximalIdeal R) hm
  have hheight : (maximalIdeal R).height = 2 :=
    WithBot.coe_injective (maximalIdeal_height_eq_ringKrullDim.trans hdim)
  rw [hheight] at hh
  norm_num at hh

omit [IsDomain R] [IsNoetherianRing R] in
private theorem parameter_pair_eq_of_mem_maximal_mul
    (f g h : R)
    (hh : h ∈ maximalIdeal R * (Ideal.span {f} ⊔ Ideal.span {g})) :
    Ideal.span {f + h} ⊔ Ideal.span {g} = Ideal.span {f} ⊔ Ideal.span {g} := by
  rw [Ideal.mul_sup] at hh
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hh
  obtain ⟨s, hs, hsf⟩ := Ideal.mem_mul_span_singleton.mp hu
  obtain ⟨t, _, htg⟩ := Ideal.mem_mul_span_singleton.mp hv
  have hform : f + h = (1 + s) * f + t * g := by
    rw [← huv, ← hsf, ← htg]
    ring
  have hsunit : IsUnit (1 + s) := by
    have hn : -s ∈ nonunits R := (maximalIdeal R).neg_mem hs
    simpa only [sub_neg_eq_add] using isUnit_one_sub_self_of_mem_nonunits (-s) hn
  have hspan : Ideal.span {(1 + s) * f} = Ideal.span {f} := by
    rw [← Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_eq_top.mpr hsunit, Ideal.top_mul]
  calc
    Ideal.span {f + h} ⊔ Ideal.span {g} = Ideal.span {f + h, g} :=
      (Ideal.span_insert _ _).symm
    _ = Ideal.span {(1 + s) * f, g} := by
      rw [hform, Ideal.span_pair_add_mul_right]
    _ = Ideal.span {f} ⊔ Ideal.span {g} := by rw [Ideal.span_insert, hspan]

/-- A prescribed nonzero nonunit on a local Noetherian surface admits a
parameter pair whose ideal is unchanged by every sufficiently deep
perturbation of the prescribed element. Every such perturbation is nonzero. -/
theorem exists_stable_parameter_pair (hdim : ringKrullDim R = 2)
    (a : R) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal R) :
    ∃ g : R, g ∈ maximalIdeal R ∧
      (Ideal.span {a} ⊔ Ideal.span {g}).radical = maximalIdeal R ∧
      ∃ N : ℕ, 0 < N ∧ ∀ h ∈ maximalIdeal R ^ N,
        Ideal.span {a + h} ⊔ Ideal.span {g} = Ideal.span {a} ⊔ Ideal.span {g} ∧
          a + h ≠ 0 := by
  let : Ring.KrullDimLE 2 R := Ring.krullDimLE_iff.mpr hdim.le
  obtain ⟨g, hg, hrad⟩ := exists_parameter_pair_containing R a ha0 ha
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (show maximalIdeal R ≤ (Ideal.span {a} ⊔ Ideal.span {g}).radical by rw [hrad])
    (maximalIdeal R).fg_of_isNoetherianRing
  refine ⟨g, hg, hrad, n + 1, Nat.succ_pos _, ?_⟩
  intro h hh
  have hle : maximalIdeal R ^ (n + 1) ≤
      maximalIdeal R * (Ideal.span {a} ⊔ Ideal.span {g}) := by
    rw [pow_succ']
    exact mul_le_mul' le_rfl hn
  have he := parameter_pair_eq_of_mem_maximal_mul a g h (hle hh)
  exact ⟨he, ne_zero_of_parameter_pair hdim (a + h) g (by rw [he, hrad])⟩

end IsLocalRing

namespace Module

private theorem scalarCokernel_quotient_length
    {R : Type*} [CommRing R] (I : Ideal R) (g : R) :
    Module.length R (ScalarCokernel (R ⧸ I) g) =
      Module.length R (R ⧸ (I ⊔ Ideal.span {g})) := by
  let q : (R ⧸ I) →ₗ[R] (R ⧸ (I ⊔ Ideal.span {g})) := Submodule.factor le_sup_left
  have hker : LinearMap.ker q = LinearMap.range (LinearMap.lsmul R (R ⧸ I) g) := by
    ext z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    constructor
    · intro hx
      have hxI : x ∈ I ⊔ Ideal.span {g} := Ideal.Quotient.eq_zero_iff_mem.mp hx
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxI
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hv
      refine ⟨Ideal.Quotient.mk I w, ?_⟩
      change Ideal.Quotient.mk I g * Ideal.Quotient.mk I w = Ideal.Quotient.mk I x
      rw [← map_mul, ← hw, ← huv, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hu,
        zero_add]
    · rintro ⟨z, hz⟩
      rw [← hz]
      change q (g • z) = 0
      rw [q.map_smul]
      change Ideal.Quotient.mk (I ⊔ Ideal.span {g}) g * q z = 0
      have hgI : g ∈ I ⊔ Ideal.span {g} :=
        (show Ideal.span {g} ≤ I ⊔ Ideal.span {g} from le_sup_right)
          (Ideal.mem_span_singleton_self g)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hgI, zero_mul]
  change Module.length R ((R ⧸ I) ⧸ LinearMap.range (LinearMap.lsmul R (R ⧸ I) g)) = _
  rw [← hker]
  exact (q.quotKerEquivOfSurjective (Submodule.factor_surjective le_sup_left)).length_eq

private theorem minimalPrime_count_le_scalarCokernel
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M g)
    (hfin : Module.length R (ScalarCokernel M g) ≠ ⊤) :
    (moduleMinimalPrimes (A := R) M).card ≤ (Module.length R (ScalarCokernel M g)).toNat := by
  classical
  obtain ⟨D⟩ := nonempty_primeFiltration (A := R) M
  have hterm (P : Ideal R) (hP : P ∈ moduleMinimalPrimes (A := R) M) :
      (1 : ℤ) ≤ minimalPrimeCokernelTerm M g P := by
    have hmin := (mem_moduleMinimalPrimes P).mp hP
    let : P.IsPrime := hmin.isPrime
    have hlocal := D.localized_length_eq_count_of_bot P hmin
    have hcount : 0 < D.primes.count P :=
      List.count_pos_iff.mpr (D.minimalPrime_mem_primes P hmin)
    have hfactorfin := (finitePrincipal_minimalPrime g hfin P hmin).2
    have hsupp : (Module.support R (ScalarCokernel (R ⧸ P) g)).Nonempty := by
      refine ⟨⟨IsLocalRing.maximalIdeal R, inferInstance⟩, ?_⟩
      rw [support_scalarCokernel]
      refine ⟨?_, Set.singleton_subset_iff.mpr hg⟩
      apply Module.mem_support_iff_of_finite.mpr
      rw [Ideal.annihilator_quotient]
      exact IsLocalRing.le_maximalIdeal hmin.isPrime.ne_top
    let : Nontrivial (ScalarCokernel (R ⧸ P) g) := Module.nonempty_support_iff.mp hsupp
    have hfactorpos : 0 < (Module.length R (ScalarCokernel (R ⧸ P) g)).toNat :=
      ENat.toNat_pos Module.length_pos.ne' hfactorfin
    rw [minimalPrimeCokernelTerm, dite_eq_left hmin, hlocal, ENat.toNat_natCast]
    have hpos : 0 < D.primes.count P *
        (Module.length R (ScalarCokernel (R ⧸ P) g)).toNat := Nat.mul_pos hcount hfactorpos
    have hnat : 1 ≤ D.primes.count P *
        (Module.length R (ScalarCokernel (R ⧸ P) g)).toNat := hpos
    exact_mod_cast hnat
  have hsum : ((moduleMinimalPrimes (A := R) M).card : ℤ) ≤
      ((Module.length R (ScalarCokernel M g)).toNat : ℤ) := by
    rw [principalCokernel_associativity g hg hreg hfin]
    calc
      ((moduleMinimalPrimes (A := R) M).card : ℤ) =
          ∑ P ∈ moduleMinimalPrimes (A := R) M, (1 : ℤ) := by simp
      _ ≤ ∑ P ∈ moduleMinimalPrimes (A := R) M, minimalPrimeCokernelTerm M g P :=
        Finset.sum_le_sum hterm
  exact_mod_cast hsum

end Module

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsNoetherianRing R] [IsIntegrallyClosed R]

private theorem parameter_regular_on_principal_quotient
    (hdim : ringKrullDim R = 2) (f g : R) (hf : f ≠ 0)
    (hrad : (Ideal.span {f} ⊔ Ideal.span {g}).radical = maximalIdeal R) :
    IsSMulRegular (R ⧸ Ideal.span {f}) g := by
  intro x y hxy
  change g • x = g • y at hxy
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R (x - y) hne
  have hfP : f ∈ P := by
    apply hle
    rw [Submodule.mem_colon_singleton]
    change Ideal.Quotient.mk (Ideal.span {f}) f * (x - y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f), zero_mul]
  have hgP : g ∈ P := by
    apply hle
    rw [Submodule.mem_colon_singleton]
    change g • (x - y) = 0
    rw [smul_sub, hxy, sub_self]
  have hIP : Ideal.span {f} ⊔ Ideal.span {g} ≤ P :=
    sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hfP)
      ((Ideal.span_singleton_le_iff_mem P).mpr hgP)
  have hmP : maximalIdeal R ≤ P := by
    rw [← hrad]
    exact hP.isPrime.radical_le_iff.mpr hIP
  have he : P = maximalIdeal R := le_antisymm (le_maximalIdeal hP.isPrime.ne_top) hmP
  have hh := hP.height_le_one_of_principal hf
  have hheight : (maximalIdeal R).height = 2 :=
    WithBot.coe_injective (maximalIdeal_height_eq_ringKrullDim.trans hdim)
  rw [he, hheight] at hh
  norm_num at hh

omit [IsDomain R] [IsIntegrallyClosed R] in
private theorem parameter_quotient_length_ne_top (f g : R)
    (hrad : (Ideal.span {f} ⊔ Ideal.span {g}).radical = maximalIdeal R) :
    Module.length R (R ⧸ (Ideal.span {f} ⊔ Ideal.span {g})) ≠ ⊤ := by
  apply Module.length_ne_top_iff.mpr
  apply Module.finiteLength_of_support_maximal R
  intro P hP
  have hIP := Module.annihilator_le_of_mem_support hP
  rw [Ideal.annihilator_quotient] at hIP
  have hmP : maximalIdeal R ≤ P.asIdeal := by
    rw [← hrad]
    exact P.isPrime.radical_le_iff.mpr hIP
  have he : P.asIdeal = maximalIdeal R :=
    le_antisymm (le_maximalIdeal P.isPrime.ne_top) hmP
  rw [he]
  infer_instance

/-- The number of minimal primes of a nonzero principal quotient is bounded
by the length of an actual parameter quotient on a normal local surface. -/
theorem principal_minimalPrimes_card_le_parameter_length
    (hdim : ringKrullDim R = 2) (f g : R) (hf : f ≠ 0)
    (hg : g ∈ maximalIdeal R)
    (hrad : (Ideal.span {f} ⊔ Ideal.span {g}).radical = maximalIdeal R) :
    (Module.moduleMinimalPrimes (A := R) (R ⧸ Ideal.span {f})).card ≤
      (Module.length R (R ⧸ (Ideal.span {f} ⊔ Ideal.span {g}))).toNat := by
  have hlen := Module.scalarCokernel_quotient_length (Ideal.span {f}) g
  have hfin : Module.length R (Module.ScalarCokernel (R ⧸ Ideal.span {f}) g) ≠ ⊤ := by
    rw [hlen]
    exact parameter_quotient_length_ne_top f g hrad
  have h := Module.minimalPrime_count_le_scalarCokernel g hg
    (parameter_regular_on_principal_quotient hdim f g hf hrad) hfin
  rwa [hlen] at h

/-- A fixed original parameter quotient bounds the number of minimal primes
throughout the actual stable perturbation family. -/
theorem exists_stable_parameter_pair_with_prime_count_bound
    (hdim : ringKrullDim R = 2) (a : R) (ha0 : a ≠ 0)
    (ha : a ∈ maximalIdeal R) :
    ∃ g : R, g ∈ maximalIdeal R ∧
      (Ideal.span {a} ⊔ Ideal.span {g}).radical = maximalIdeal R ∧
      ∃ N : ℕ, 0 < N ∧ ∀ h ∈ maximalIdeal R ^ N,
        Ideal.span {a + h} ⊔ Ideal.span {g} = Ideal.span {a} ⊔ Ideal.span {g} ∧
          a + h ≠ 0 ∧
          (Module.moduleMinimalPrimes (A := R) (R ⧸ Ideal.span {a + h})).card ≤
            (Module.length R (R ⧸ (Ideal.span {a} ⊔ Ideal.span {g}))).toNat := by
  obtain ⟨g, hg, hrad, N, hN, hstable⟩ := exists_stable_parameter_pair hdim a ha0 ha
  refine ⟨g, hg, hrad, N, hN, ?_⟩
  intro h hh
  obtain ⟨he, hne⟩ := hstable h hh
  refine ⟨he, hne, ?_⟩
  have hb := principal_minimalPrimes_card_le_parameter_length hdim (a + h) g hne hg
    (by rw [he, hrad])
  rwa [he] at hb

end IsLocalRing

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [IsLocalRing R]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] in
private abbrev coverSymbolicSquare (P : PrimeSpectrum R) : Ideal R :=
  ((maximalIdeal (Localization.AtPrime P.asIdeal)) ^ 2).comap
    (algebraMap R (Localization.AtPrime P.asIdeal))

omit [IsLocalRing R] in
private theorem cover_not_le_square (P : PrimeSpectrum R) (hP : P.asIdeal.height = 1) :
    ¬P.asIdeal ≤ coverSymbolicSquare P := by
  let S := Localization.AtPrime P.asIdeal
  let : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one P.asIdeal S hP
  intro h
  have hm : maximalIdeal S ≤ maximalIdeal S ^ 2 := by
    have hm' := Ideal.map_le_iff_le_comap.mpr h
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal] at hm'
    exact hm'
  have hmzero : maximalIdeal S = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) (maximalIdeal S)
      (maximalIdeal S).fg_of_isNoetherianRing
      (by simpa only [smul_eq_mul, pow_two] using hm)
      (by simp [IsLocalRing.jacobson_eq_maximalIdeal])
  exact IsDiscreteValuationRing.not_a_field S hmzero

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
private theorem cover_maximal_not_le (hdim : ringKrullDim R = 2)
    (P : PrimeSpectrum R) (hP : P.asIdeal.height = 1) :
    ¬maximalIdeal R ≤ P.asIdeal := by
  intro h
  have he : maximalIdeal R = P.asIdeal :=
    le_antisymm h (le_maximalIdeal P.isPrime.ne_top)
  have hm : (maximalIdeal R).height = 2 :=
    WithBot.coe_injective (maximalIdeal_height_eq_ringKrullDim.trans hdim)
  rw [he, hP] at hm
  norm_num at hm

omit [IsLocalRing R] in
private theorem cover_exists_simple_element
    (S : Finset (PrimeSpectrum R)) (hS : ∀ P ∈ S, P.asIdeal.height = 1)
    (P : PrimeSpectrum R) (hP : P ∈ S) :
    ∃ t : R, t ∈ P.asIdeal ∧ t ∉ coverSymbolicSquare P ∧
      ∀ Q ∈ S, Q ≠ P → t ∉ Q.asIdeal := by
  classical
  let T : Set (Ideal R) := insert (coverSymbolicSquare P)
    (PrimeSpectrum.asIdeal '' ((S : Set (PrimeSpectrum R)) \ {P}))
  have hT : T.Finite := ((S.finite_toSet.sdiff (t := {P})).image _).insert _
  have hnot : ¬(P.asIdeal : Set R) ⊆ ⋃ I ∈ T, (I : Set R) := by
    rw [Ideal.subset_union_prime_finite hT (coverSymbolicSquare P) (coverSymbolicSquare P)
      (fun I hI hne _ => by
        obtain ⟨Q, _, rfl⟩ := (Set.mem_insert_iff.mp hI).resolve_left hne
        exact Q.isPrime)]
    rintro ⟨I, hI, hPI⟩
    rcases Set.mem_insert_iff.mp hI with rfl | hI
    · exact cover_not_le_square P (hS P hP) hPI
    · obtain ⟨Q, ⟨hQ, hQP⟩, rfl⟩ := hI
      have he : P.asIdeal = Q.asIdeal :=
        Ideal.eq_of_le_of_height_le P.asIdeal hPI (by rw [hS Q hQ, hS P hP])
      exact hQP (Set.mem_singleton_iff.mpr (PrimeSpectrum.ext he.symm))
  obtain ⟨t, htP, ht⟩ := Set.not_subset.mp hnot
  refine ⟨t, htP, ?_, ?_⟩
  · intro hts
    exact ht (Set.mem_iUnion₂.mpr ⟨coverSymbolicSquare P, Set.mem_insert _ _, hts⟩)
  · intro Q hQ hQP htQ
    exact ht (Set.mem_iUnion₂.mpr ⟨Q.asIdeal,
      Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ ⟨hQ, by simpa using hQP⟩), htQ⟩)

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
private theorem cover_exists_deep_avoiding (hdim : ringKrullDim R = 2)
    (S : Finset (PrimeSpectrum R)) (hS : ∀ P ∈ S, P.asIdeal.height = 1) (N : ℕ) :
    ∃ z : R, z ∈ maximalIdeal R ^ N ∧ ∀ P ∈ S, z ∉ P.asIdeal := by
  classical
  let T : Set (Ideal R) := PrimeSpectrum.asIdeal '' (S : Set (PrimeSpectrum R))
  have hT : T.Finite := S.finite_toSet.image _
  have hnot : ¬((maximalIdeal R ^ N : Ideal R) : Set R) ⊆ ⋃ I ∈ T, (I : Set R) := by
    rw [Ideal.subset_union_prime_finite hT (⊥ : Ideal R) (⊥ : Ideal R)
      (fun I hI _ _ => by obtain ⟨P, _, rfl⟩ := hI; exact P.isPrime)]
    rintro ⟨I, ⟨P, hP, rfl⟩, hle⟩
    by_cases hN : N = 0
    · have htop : (⊤ : Ideal R) ≤ P.asIdeal := by simpa [hN] using hle
      exact P.isPrime.ne_top (top_le_iff.mp htop)
    · exact cover_maximal_not_le hdim P (hS P hP) (Ideal.IsPrime.pow_le_iff hN |>.mp hle)
  obtain ⟨z, hz, hzT⟩ := Set.not_subset.mp hnot
  refine ⟨z, hz, ?_⟩
  intro P hP hzP
  exact hzT (Set.mem_iUnion₂.mpr ⟨P.asIdeal, Set.mem_image_of_mem _ hP, hzP⟩)

private theorem cover_local_span_eq_maximal
    (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (x : S) (hx : x ∈ maximalIdeal S) (hx2 : x ∉ maximalIdeal S ^ 2) :
    Ideal.span {x} = maximalIdeal S := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hm : maximalIdeal S = Ideal.span {t} := ht.maximalIdeal_eq
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (hm ▸ hx)
  have hyunit : IsUnit y := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hyM
    apply hx2
    rw [hy, pow_two]
    exact Ideal.mul_mem_mul (hm.symm ▸ Ideal.mem_span_singleton_self t) hyM
  rw [hy, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_top.mpr hyunit, Ideal.mul_top, ← hm]

private theorem cover_exists_deep_simple_perturbation
    (hdim : ringKrullDim R = 2) (f : R) (S : Finset (PrimeSpectrum R))
    (hS : ∀ P ∈ S, P.asIdeal.height = 1)
    (hf : ∀ P ∈ S, f ∈ P.asIdeal) (N : ℕ) :
    ∃ h : R, h ∈ maximalIdeal R ^ N ∧
      ∀ P ∈ S, f + h ∈ P.asIdeal ∧ f + h ∉ coverSymbolicSquare P := by
  classical
  choose t ht using fun P : S => cover_exists_simple_element S hS P.val P.property
  obtain ⟨z, hz, hzavoid⟩ := cover_exists_deep_avoiding hdim S hS N
  let e : S → ℕ := fun P => if f ∈ coverSymbolicSquare P.val then 1 else 2
  let u : R := ∏ P : S, t P ^ e P
  refine ⟨z * u, (maximalIdeal R ^ N).mul_mem_right _ hz, ?_⟩
  intro P hP
  let q : S := ⟨P, hP⟩
  let w : R := ∏ Q ∈ (Finset.univ : Finset S).erase q, t Q ^ e Q
  have hu : u = t q ^ e q * w :=
    (Finset.mul_prod_erase Finset.univ (fun Q : S => t Q ^ e Q) (Finset.mem_univ q)).symm
  have hepos : 0 < e q := by simp only [e]; split_ifs <;> decide
  have hup : u ∈ P.asIdeal := by
    rw [hu]
    exact P.asIdeal.mul_mem_right _ (P.asIdeal.pow_mem_of_mem (ht q).1 _ hepos)
  have hhp : z * u ∈ P.asIdeal := P.asIdeal.mul_mem_left _ hup
  refine ⟨P.asIdeal.add_mem (hf P hP) hhp, ?_⟩
  let L := Localization.AtPrime P.asIdeal
  let m := maximalIdeal L
  have hzunit : IsUnit (algebraMap R L z) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff L P.asIdeal z).mpr (hzavoid P hP)
  have hwunit : IsUnit (algebraMap R L w) := by
    change IsUnit (algebraMap R L (∏ Q ∈ (Finset.univ : Finset S).erase q, t Q ^ e Q))
    rw [map_prod]
    apply IsUnit.prod_iff.mpr
    intro Q hQ
    rw [map_pow]
    apply IsUnit.pow
    apply (IsLocalization.AtPrime.isUnit_to_map_iff L P.asIdeal (t Q)).mpr
    apply (ht Q).2.2 P hP
    intro hPQ
    exact (Finset.mem_erase.mp hQ).1 (Subtype.ext hPQ.symm)
  by_cases hfsq : f ∈ coverSymbolicSquare P
  · have he : e q = 1 := ite_eq_left hfsq
    have hhnot : z * u ∉ coverSymbolicSquare P := by
      change algebraMap R L (z * u) ∉ m ^ 2
      rw [map_mul, hu, map_mul, map_pow, he, pow_one,
        (m ^ 2).unit_mul_mem_iff_mem hzunit, (m ^ 2).mul_unit_mem_iff_mem hwunit]
      exact (ht q).2.1
    intro hsum
    apply hhnot
    simpa only [add_sub_cancel_left] using (coverSymbolicSquare P).sub_mem hsum hfsq
  · have he : e q = 2 := ite_eq_right hfsq
    have htmem : algebraMap R L (t q) ∈ m :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L P.asIdeal _).mpr (ht q).1
    have hhsq : z * u ∈ coverSymbolicSquare P := by
      change algebraMap R L (z * u) ∈ m ^ 2
      rw [map_mul, hu, map_mul, map_pow, he]
      apply (m ^ 2).mul_mem_left
      apply (m ^ 2).mul_mem_right
      simpa only [pow_two] using Ideal.mul_mem_mul htmem htmem
    intro hsum
    apply hfsq
    simpa only [add_sub_cancel_right] using (coverSymbolicSquare P).sub_mem hsum hhsq

omit [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] in
private def coverPrincipalPrimes (f : R) : Finset (PrimeSpectrum R) :=
  (Module.moduleMinimalPrimes (A := R) (R ⧸ Ideal.span {f})).attach.map
    { toFun := fun P => ⟨P.val, ((Module.mem_moduleMinimalPrimes P.val).mp P.property).isPrime⟩
      inj' := fun _ _ h => Subtype.ext (congrArg PrimeSpectrum.asIdeal h) }

omit [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] in
private theorem coverPrincipalPrimes_card (f : R) :
    (coverPrincipalPrimes f).card =
      (Module.moduleMinimalPrimes (A := R) (R ⧸ Ideal.span {f})).card := by
  simp [coverPrincipalPrimes]

omit [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] in
private theorem mem_coverPrincipalPrimes (f : R) (P : PrimeSpectrum R) :
    P ∈ coverPrincipalPrimes f ↔ P.asIdeal ∈ (Ideal.span {f}).minimalPrimes := by
  constructor
  · intro h
    obtain ⟨Q, _, rfl⟩ := Finset.mem_map.mp h
    change Q.val ∈ (Ideal.span {f}).minimalPrimes
    simpa only [Ideal.annihilator_quotient] using
      (Module.mem_moduleMinimalPrimes Q.val).mp Q.property
  · intro h
    have hP : P.asIdeal ∈ Module.moduleMinimalPrimes (A := R) (R ⧸ Ideal.span {f}) :=
      (Module.mem_moduleMinimalPrimes P.asIdeal).mpr
        (by simpa only [Ideal.annihilator_quotient] using h)
    exact Finset.mem_map.mpr ⟨⟨P.asIdeal, hP⟩, Finset.mem_attach _ _, PrimeSpectrum.ext rfl⟩

omit [IsIntegrallyClosed R] [IsLocalRing R] in
private theorem coverPrincipalPrimes_height (f : R) (hf : f ≠ 0)
    (P : PrimeSpectrum R) (hP : P ∈ coverPrincipalPrimes f) : P.asIdeal.height = 1 :=
  Ideal.height_eq_one_of_mem_minimalPrimes_span hf ((mem_coverPrincipalPrimes f P).mp hP)

omit [IsIntegrallyClosed R] [IsLocalRing R] in
private theorem mem_coverPrincipalPrimes_of_height_one (f : R) (hf : f ≠ 0)
    (P : PrimeSpectrum R) (hP : P.asIdeal.height = 1) (hfP : f ∈ P.asIdeal) :
    P ∈ coverPrincipalPrimes f := by
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem P.asIdeal).mpr hfP)
  let : Q.IsPrime := hQ.isPrime
  have hQheight := Ideal.height_eq_one_of_mem_minimalPrimes_span hf hQ
  have he : Q = P.asIdeal := Ideal.eq_of_le_of_height_le Q hQP (by rw [hP, hQheight])
  exact (mem_coverPrincipalPrimes f P).mpr (he ▸ hQ)

/-- A nonzero nonunit in a normal Noetherian local domain of dimension two
has a nonzero reduced principal cover whose positive power it divides. -/
theorem exists_reduced_principal_cover (hdim : ringKrullDim R = 2)
    (a : R) (ha0 : a ≠ 0) (hna : ¬ IsUnit a) :
    ∃ c : R, c ≠ 0 ∧ c ∈ maximalIdeal R ∧
      IsReduced (R ⧸ Ideal.span {c}) ∧ ∃ r : ℕ, 0 < r ∧ a ∣ c ^ r := by
  classical
  have ham : a ∈ maximalIdeal R := hna
  obtain ⟨g, _, hrad, N, _, hstable⟩ :=
    exists_stable_parameter_pair_with_prime_count_bound hdim a ha0 ham
  let B := (Module.length R (R ⧸ (Ideal.span {a} ⊔ Ideal.span {g}))).toNat
  let admissible : R → Prop := fun h => h ∈ maximalIdeal R ^ N ∧
    ∀ P ∈ coverPrincipalPrimes a, h ∈ P.asIdeal
  have hzero : admissible 0 := ⟨(maximalIdeal R ^ N).zero_mem, fun P _ => P.asIdeal.zero_mem⟩
  have hbound (h : R) (hh : h ∈ maximalIdeal R ^ N) :
      (coverPrincipalPrimes (a + h)).card ≤ B := by
    rw [coverPrincipalPrimes_card]
    exact (hstable h hh).2.2
  let p : ℕ → Prop := fun n => ∃ h : R, admissible h ∧
    (coverPrincipalPrimes (a + h)).card = n
  have hp : p (Nat.findGreatest p B) :=
    Nat.findGreatest_spec (hbound 0 hzero.1) ⟨0, hzero, rfl⟩
  obtain ⟨h₀, hh₀, hcount⟩ := hp
  let f := a + h₀
  have hf : f ≠ 0 := (hstable h₀ hh₀.1).2.1
  have hmax (h : R) (hh : admissible h) :
      (coverPrincipalPrimes (a + h)).card ≤ (coverPrincipalPrimes f).card := by
    rw [hcount]
    exact Nat.le_findGreatest (hbound h hh.1) ⟨h, hh, rfl⟩
  have hsub : coverPrincipalPrimes a ⊆ coverPrincipalPrimes f := by
    intro P hP
    apply mem_coverPrincipalPrimes_of_height_one f hf P (coverPrincipalPrimes_height a ha0 P hP)
    exact P.asIdeal.add_mem
      (((mem_coverPrincipalPrimes a P).mp hP).le (Ideal.mem_span_singleton_self a))
      (hh₀.2 P hP)
  have hfmem (P : PrimeSpectrum R) (hP : P ∈ coverPrincipalPrimes f) : f ∈ P.asIdeal :=
    ((mem_coverPrincipalPrimes f P).mp hP).le (Ideal.mem_span_singleton_self f)
  obtain ⟨h₁, hh₁, hsimple⟩ := cover_exists_deep_simple_perturbation hdim f
    (coverPrincipalPrimes f) (coverPrincipalPrimes_height f hf) hfmem N
  have hnew : admissible (h₀ + h₁) := by
    refine ⟨(maximalIdeal R ^ N).add_mem hh₀.1 hh₁, ?_⟩
    intro P hP
    apply P.asIdeal.add_mem (hh₀.2 P hP)
    simpa only [add_sub_cancel_left] using
      P.asIdeal.sub_mem (hsimple P (hsub hP)).1 (hfmem P (hsub hP))
  let c := a + (h₀ + h₁)
  have hc : c ≠ 0 := (hstable (h₀ + h₁) hnew.1).2.1
  have hceq : c = f + h₁ := (add_assoc a h₀ h₁).symm
  have hsub' : coverPrincipalPrimes f ⊆ coverPrincipalPrimes c := by
    intro P hP
    apply mem_coverPrincipalPrimes_of_height_one c hc P (coverPrincipalPrimes_height f hf P hP)
    rw [hceq]
    exact (hsimple P hP).1
  have hsets : coverPrincipalPrimes c = coverPrincipalPrimes f :=
    (Finset.eq_of_subset_of_card_le hsub' (hmax (h₀ + h₁) hnew)).symm
  have hcrad : (Ideal.span {c} ⊔ Ideal.span {g}).radical = maximalIdeal R := by
    rw [(hstable (h₀ + h₁) hnew.1).1, hrad]
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · rw [← hcrad]
    have hcI : c ∈ Ideal.span {c} ⊔ Ideal.span {g} :=
      (show Ideal.span {c} ≤ Ideal.span {c} ⊔ Ideal.span {g} from le_sup_left)
        (Ideal.mem_span_singleton_self c)
    exact Ideal.le_radical hcI
  · apply IsIntegrallyClosed.isReduced_quotient_span_singleton_of_height_one c hc
    intro P hP hheight
    let Q : PrimeSpectrum R := ⟨P, hP⟩
    let L := Localization.AtPrime P
    let : IsDiscreteValuationRing L :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one P L hheight
    by_cases hcP : c ∈ P
    · have hQc : Q ∈ coverPrincipalPrimes c :=
        mem_coverPrincipalPrimes_of_height_one c hc Q hheight hcP
      have hQf : Q ∈ coverPrincipalPrimes f := hsets ▸ hQc
      have hcnot : c ∉ coverSymbolicSquare Q := by
        rw [hceq]
        exact (hsimple Q hQf).2
      have hcm : algebraMap R L c ∈ maximalIdeal L :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff L P c).mpr hcP
      have hspan := cover_local_span_eq_maximal L (algebraMap R L c) hcm hcnot
      rw [Ideal.map_span, Set.image_singleton, hspan]
      exact (maximalIdeal.isMaximal L).isPrime.isRadical
    · have hcunit : IsUnit (algebraMap R L c) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff L P c).mpr hcP
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top.mpr hcunit]
      apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr
      intro x _
      exact Submodule.mem_top
  · apply Ideal.exists_pos_pow_dvd_of_mem_minimalPrimes a c
    intro P hP
    let Q : PrimeSpectrum R := ⟨P, hP.isPrime⟩
    exact P.add_mem (hP.le (Ideal.mem_span_singleton_self a))
      (hnew.2 Q ((mem_coverPrincipalPrimes a Q).mpr hP))

end IsLocalRing
