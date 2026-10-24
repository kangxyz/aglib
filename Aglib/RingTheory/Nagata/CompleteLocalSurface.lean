/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.CompleteCurve
public import Aglib.RingTheory.LocalRing.FiniteRegularSubring
public import Aglib.RingTheory.Nagata.CompleteSurface
public import Aglib.RingTheory.Nagata.Completion
public import Aglib.RingTheory.Nagata.Normalization
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Mathlib.Data.ENat.SuccOrder

/-!
# Complete local rings of dimension at most two are Nagata

The dimension-two domain case uses the actual finite regular complete
subring map, regular-local normality, the proved normal-surface Nagata
property, and finite ascent. The lower-dimensional domain case uses the
complete-curve normalization theorem. Literal prime quotients then give
the Nagata property without a domain or reducedness assumption on the
original complete local ring. The reduced case has finite normalization
in its supplied total quotient ring.

The original scalar maps are retained. All rings and tested fields lie
in one ambient universe, with auxiliary Japanese test universe zero.
No finite-type stability or resolution theorem is used.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

/-- A complete Noetherian local domain of dimension at most two is
Japanese. Its normality is derived only for the actual regular source
constructed in dimension two, not assumed for the original domain. -/
theorem IsJapaneseRing.of_complete_local_dimLE_two
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 2 A]
    [IsAdicComplete (maximalIdeal A) A] : IsJapaneseRing.{u, 0} A := by
  by_cases hd : ringKrullDim A = 2
  · obtain ⟨R, hR, hD, hcomplete, hdR, f, _, _, hfinite⟩ :=
      IsLocalRing.exists_finite_complete_regular_subring A hd
    let : IsRegularLocalRing R := hR
    let : IsDomain R := hD
    let : IsAdicComplete (maximalIdeal R) R := hcomplete
    let : Ring.KrullDimLE 2 R := Ring.krullDimLE_iff.mpr hdR.le
    let : IsIntegrallyClosed R := IsRegularLocalRing.isIntegrallyClosed_of_regularLocal R
    let : Algebra R A := f.toAlgebra
    let : Module.Finite R A := hfinite
    have hRnagata : IsNagataRing.{u, 0} R :=
      IsNagataRing.of_complete_local_normal_dimLE_two R
    have hAnagata : IsNagataRing.{u, 0} A := hRnagata.of_finite
    exact hAnagata.isJapaneseRing
  · have hlt : ringKrullDim A < 2 :=
      lt_of_le_of_ne (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 A)) hd
    let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr
      ((ENat.WithBot.lt_add_one_iff (m := 1)).mp (by
        convert hlt using 1
        norm_num))
    intro L hL hKL hAL hT hfin
    exact integralClosure.finite_of_complete_local_dimLE_one A (FractionRing A) L

/-- Every complete Noetherian local ring of dimension at most two is
Nagata. Every tested prime quotient is the actual quotient, with its
original maximal-adic completeness and fraction-field coefficient map. -/
theorem IsNagataRing.of_complete_local_dimLE_two
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Ring.KrullDimLE 2 A] [IsAdicComplete (maximalIdeal A) A] :
    IsNagataRing.{u, 0} A := by
  refine ⟨inferInstance, ?_⟩
  intro p hp
  let : IsNoetherianRing (A ⧸ p) := isNoetherianRing_of_surjective A (A ⧸ p)
    (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : IsLocalRing (A ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : Ring.KrullDimLE 2 (A ⧸ p) := Ring.krullDimLE_iff.mpr
    ((ringKrullDim_quotient_le p).trans
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 A)))
  let : IsAdicComplete (maximalIdeal (A ⧸ p)) (A ⧸ p) := by
    have h := IsAdicComplete.map_algebraMap_of_finite A (maximalIdeal A) (A ⧸ p)
    rwa [IsLocalRing.map_maximalIdeal_of_surjective
      (algebraMap A (A ⧸ p)) Ideal.Quotient.mk_surjective] at h
  exact IsJapaneseRing.of_complete_local_dimLE_two (A ⧸ p)

/-- CN2 for the literal integral closure in any finite extension of a
supplied actual fraction field. The original action of the complete
local domain on the ambient extension field is unchanged. -/
theorem integralClosure.finite_of_complete_local_dimLE_two
    (A K L : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 2 A]
    [IsAdicComplete (maximalIdeal A) A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] : Module.Finite A (integralClosure A L) :=
  (IsJapaneseRing.of_complete_local_dimLE_two A).finite_integralClosure_of_isFractionRing K L

/-- A local domain finite over the original complete local ring of
dimension at most two has reduced maximal-adic completion. This uses
finite Nagata ascent and the proved dimension-bounded completion theorem;
the finite algebra itself need not be normal or complete. -/
theorem AdicCompletion.isReduced_of_finite_over_complete_local_dimLE_two
    (A B : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Ring.KrullDimLE 2 A] [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B] [Module.Finite A B] :
    IsReduced (AdicCompletion (maximalIdeal B) B) := by
  have hB : IsNagataRing.{u, 0} B :=
    (IsNagataRing.of_complete_local_dimLE_two A).of_finite
  let : Algebra.IsIntegral A B := inferInstance
  have hdim : ringKrullDim B ≤ ringKrullDim A := by
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B))
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under (R := A) hpq
  exact hB.isReduced_completion_of_dimLE_two
    (hdim.trans (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 A)))

/-- CR2: the literal normalization of a complete reduced Noetherian local
ring of dimension at most two in its original total quotient ring is finite. -/
theorem integralClosure.finite_of_complete_local_reduced_dimLE_two
    (R : Type u) [CommRing R] [IsReduced R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 2 R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (Q : Type v) [CommRing Q] [Algebra R Q] [IsFractionRing R Q] :
    Module.Finite R (integralClosure R Q) :=
  integralClosure.finite_of_isNagataRing R (IsNagataRing.of_complete_local_dimLE_two R) Q
