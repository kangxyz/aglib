/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BranchFractionAlgebra
public import Aglib.RingTheory.DiscreteValuationRing.FractionAway
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finiteness of the actual completed branch fraction fields

Localizing the finite completed-base module at a base uniformizer gives the
finite-dimensional field extension for the actual lifted fraction-field action.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing

universe u

variable (R S : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]

/-- Each actual completed branch fraction field is finite over the completed base fraction field. -/
theorem localCompletionFractionFinite
    (hI : (maximalIdeal R).map (algebraMap R S) ≠ 0)
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) hI q
    letI := localCompletionFractionAlgebra R S hI q
    Module.Finite (FractionRing (AdicCompletion (maximalIdeal R) R))
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) hI q
  let := localCompletionFractionAlgebra R S hI q
  have := localCompletionFractionIsScalarTower R S hI q
  have := localCompletionBaseFinite (maximalIdeal R) hI q
  have := localCompletionBase_isLocalHom R S hI q
  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (AdicCompletion (maximalIdeal R) R)
  have : IsLocalization.Away π (FractionRing (AdicCompletion (maximalIdeal R) R)) :=
    IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit _ hπ.ne_zero hπ.not_isUnit
  have hn : algebraMap (AdicCompletion (maximalIdeal R) R)
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) π ≠ 0 :=
    (map_ne_zero_iff _ (localCompletionBase_injective R S hI q)).mpr hπ.ne_zero
  have hnu : ¬ IsUnit (algebraMap (AdicCompletion (maximalIdeal R) R)
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) π) :=
    fun h ↦ hπ.not_isUnit (IsUnit.of_map _ _ h)
  have : IsLocalization.Away
      (algebraMap (AdicCompletion (maximalIdeal R) R)
        (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) π)
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) :=
    IsDiscreteValuationRing.isLocalizationAway_of_nonzero_nonunit _ hn hnu
  have : IsLocalization
      (Algebra.algebraMapSubmonoid
        (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) (Submonoid.powers π))
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using this
  exact Module.Finite.of_isLocalization (AdicCompletion (maximalIdeal R) R)
    (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) (Submonoid.powers π)

end AdicCompletion
