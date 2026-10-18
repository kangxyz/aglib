/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteDedekindBranches
public import Aglib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Nonzero base uniformizers in completed Dedekind branches

Each actual prime factor gives a local DVR and its completed DVR. The image of a
base uniformizer is nonzero and a nonunit in every completed branch, including
ramified branches where that image need not itself be irreducible.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing UniqueFactorizationMonoid

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [DecidableEq (Ideal S)]

/-- The completion of the original localization at an actual prime ideal factor. -/
abbrev BranchCompletion (I : Ideal S) (q : IdealBranch I) :=
  AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val)

/-- Every original localization indexed by an ideal factor is a DVR. -/
instance idealBranchLocalizationIsDiscreteValuationRing (I : Ideal S) (q : IdealBranch I) :
    IsDiscreteValuationRing (Localization.AtPrime q.val) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
    (prime_of_normalized_factor q.val (Multiset.mem_toFinset.mp q.property)).ne_zero _

/-- The actual completion of each original localized branch is a DVR. -/
instance branchCompletionIsDiscreteValuationRing (I : Ideal S) (q : IdealBranch I) :
    IsDiscreteValuationRing (BranchCompletion I q) :=
  AdicCompletion.instIsDiscreteValuationRingMaximalIdeal _

/-- The map from the original domain into each completed branch is injective. -/
theorem branchCompletion_algebraMap_injective (I : Ideal S) (q : IdealBranch I) :
    Function.Injective (algebraMap S (BranchCompletion I q)) := by
  rw [IsScalarTower.algebraMap_eq S (Localization.AtPrime q.val) (BranchCompletion I q)]
  exact (AdicCompletion.of_injective (maximalIdeal (Localization.AtPrime q.val))
    (Localization.AtPrime q.val)).comp
      (IsLocalization.injective (Localization.AtPrime q.val) q.val.primeCompl_le_nonZeroDivisors)

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [DecidableEq (Ideal S)]

/-- Torsion-freeness keeps the base uniformizer nonzero in every actual completed branch. -/
theorem branchCompletion_uniformizer_ne_zero [Module.IsTorsionFree R S]
    {π : R} (hπ : Irreducible π)
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    algebraMap S (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
      (algebraMap R S π) ≠ 0 :=
  (map_ne_zero_iff _ (branchCompletion_algebraMap_injective _ q)).mpr
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero)

/-- The base uniformizer lies in every original branch maximal ideal, so its image
remains a nonunit after completion. -/
theorem branchCompletion_uniformizer_not_isUnit
    {π : R} (hπ : Irreducible π)
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    ¬ IsUnit (algebraMap S (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
      (algebraMap R S π)) := by
  have hle : (maximalIdeal R).map (algebraMap R S) ≤ q.val :=
    Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp q.property))
  have hmem : algebraMap R S π ∈ q.val :=
    hle (Ideal.mem_map_of_mem (algebraMap R S)
      (show π ∈ maximalIdeal R from mem_nonunits_iff.mpr hπ.not_isUnit))
  have hlocal : ¬ IsUnit (algebraMap S (Localization.AtPrime q.val) (algebraMap R S π)) := by
    exact mem_nonunits_iff.mp
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime q.val) q.val _).mpr hmem)
  rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime q.val)
    (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)]
  exact fun h ↦ hlocal (IsUnit.of_map _ _ h)

end AdicCompletion
