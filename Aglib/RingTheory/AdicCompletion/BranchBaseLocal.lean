/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BranchUniformizer
public import Aglib.RingTheory.AdicCompletion.LocalCompletionsBase

/-!
# Local injective completed-base maps to the actual branches

The actual completed-base action on each branch is local and injective. These
properties are proved from the image of a base uniformizer, not assumed as
compatibility data.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsDiscreteValuationRing

variable {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing A]

/-- A map from a DVR to a domain is injective if one uniformizer stays nonzero. -/
theorem ringHom_injective_of_irreducible_image_ne_zero [IsDomain A]
    (f : R →+* A) {π : R} (hπ : Irreducible π) (hπf : f π ≠ 0) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  by_contra hx0
  obtain ⟨n, hn⟩ := associated_pow_irreducible hx0 hπ
  have hne : f x ≠ 0 := (hn.map f).ne_zero_iff.mpr (by simpa using pow_ne_zero n hπf)
  exact hne hx

/-- A map from a DVR to a local ring is local if one uniformizer stays a nonunit. -/
theorem ringHom_isLocalHom_of_irreducible_image_not_isUnit [IsLocalRing A]
    (f : R →+* A) {π : R} (hπ : Irreducible π) (hπf : ¬ IsUnit (f π)) :
    IsLocalHom f := by
  apply ((local_hom_TFAE f).out 1 4).mpr
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
  exact mem_nonunits_iff.mpr hπf

end IsDiscreteValuationRing

namespace AdicCompletion

universe u

variable (R S : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [DecidableEq (Ideal S)]

/-- The actual completed-base map to each completed branch is injective. -/
theorem localCompletionBase_injective [Module.IsTorsionFree R S]
    (hI : (maximalIdeal R).map (algebraMap R S) ≠ 0)
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) hI q
    Function.Injective (algebraMap (AdicCompletion (maximalIdeal R) R)
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) hI q
  have := localCompletionBaseIsScalarTower (maximalIdeal R) hI q
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  apply IsDiscreteValuationRing.ringHom_injective_of_irreducible_image_ne_zero _
    (AdicCompletion.irreducible_algebraMap R π hπ)
  rw [← IsScalarTower.algebraMap_apply R (AdicCompletion (maximalIdeal R) R),
    IsScalarTower.algebraMap_apply R S]
  exact branchCompletion_uniformizer_ne_zero R S hπ q

/-- The actual completed-base map to each completed branch is a local homomorphism. -/
theorem localCompletionBase_isLocalHom
    (hI : (maximalIdeal R).map (algebraMap R S) ≠ 0)
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) hI q
    IsLocalHom (algebraMap (AdicCompletion (maximalIdeal R) R)
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) hI q
  have := localCompletionBaseIsScalarTower (maximalIdeal R) hI q
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  apply IsDiscreteValuationRing.ringHom_isLocalHom_of_irreducible_image_not_isUnit _
    (AdicCompletion.irreducible_algebraMap R π hπ)
  rw [← IsScalarTower.algebraMap_apply R (AdicCompletion (maximalIdeal R) R),
    IsScalarTower.algebraMap_apply R S]
  exact branchCompletion_uniformizer_not_isUnit R S hπ q

end AdicCompletion
