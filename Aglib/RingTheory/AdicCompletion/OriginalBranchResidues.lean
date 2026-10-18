/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BranchUniformizer

/-!
# Original localized branch residue fields

The original local maps and finite residue extensions are derived from the
actual ideal-factor divisibility, not from a false finiteness assertion for
the localized rings over the base ring.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing UniqueFactorizationMonoid

variable (R S : Type*) [CommRing R] [IsLocalRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [DecidableEq (Ideal S)]

/-- Every actual branch lies over the original maximal ideal, so its original
localization map reflects units. -/
instance originalBranchIsLocalHom
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    IsLocalHom (algebraMap R (Localization.AtPrime q.val)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hle : (maximalIdeal R).map (algebraMap R S) ≤ q.val :=
    Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp q.property))
  have hmem : algebraMap R S a ∈ q.val :=
    hle (Ideal.mem_map_of_mem _ (show a ∈ maximalIdeal R from h))
  have hh := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime q.val) q.val (algebraMap R S a)).mpr hmem
  exact hh (by simpa only [← IsScalarTower.algebraMap_apply] using ha)

/-- The original domain surjects onto the residue of its actual localization. -/
theorem originalBranchResidue_surjective
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    Function.Surjective (algebraMap S (ResidueField (Localization.AtPrime q.val))) := by
  intro a
  obtain ⟨b, hb⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal q.val
    (Localization.AtPrime q.val)).surjective a
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨s, hb⟩

/-- Finiteness is asserted for the residue field, not for the localized ring. -/
instance originalBranchResidueFinite [Module.Finite R S]
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    Module.Finite (ResidueField R) (ResidueField (Localization.AtPrime q.val)) := by
  let : Module.Finite S (ResidueField (Localization.AtPrime q.val)) :=
    Module.Finite.of_surjective (Algebra.ofId S
      (ResidueField (Localization.AtPrime q.val))).toLinearMap
        (originalBranchResidue_surjective R S q)
  let : Module.Finite R (ResidueField (Localization.AtPrime q.val)) :=
    Module.Finite.trans S _
  exact Module.Finite.of_restrictScalars_finite R (ResidueField R) _

end AdicCompletion
