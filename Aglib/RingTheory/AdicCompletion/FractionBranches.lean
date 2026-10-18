/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.LocalCompletionsBase
public import Aglib.RingTheory.AdicCompletion.BranchUniformizer
public import Aglib.RingTheory.DiscreteValuationRing.IntegralFractionAway
public import Aglib.RingTheory.DiscreteValuationRing.FractionPi
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The actual generic product of completed original branches

Invert the original base uniformizer in the proved integral completion tensor product.
This gives all original localized branch fraction fields, without a generic tensor-isomorphism
premise and without discarding ramified branches.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace AdicCompletion

open IsLocalRing
open scoped TensorProduct

universe u
variable (R S : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  (E : Type u) [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
  [IsFractionRing S E]

/-- Scalar extension of the original fraction field is the product of fraction fields
of every actual completed localized branch. -/
def tensorEquivLocalFractionFields
    (hI : (maximalIdeal R).map (algebraMap R S) ≠ 0)
    {π : R} (hπ : Irreducible π) :
    letI := fun q ↦ localCompletionBaseAlgebra (maximalIdeal R) hI q
    AdicCompletion (maximalIdeal R) R ⊗[R] E ≃ₐ[AdicCompletion (maximalIdeal R) R]
      ∀ q : IdealBranch ((maximalIdeal R).map (algebraMap R S)),
        FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) := by
  letI := fun q ↦ localCompletionBaseAlgebra (maximalIdeal R) hI q
  let D := fun q : IdealBranch ((maximalIdeal R).map (algebraMap R S)) ↦
    BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q
  let ε := tensorEquivLocalCompletionsBase (maximalIdeal R) hI
  let c : ∀ q, D q := ε (1 ⊗ₜ[R] algebraMap R S π)
  have hc (q) : c q ≠ 0 := by
    change tensorEquivLocalCompletions (maximalIdeal R) hI
      (1 ⊗ₜ[R] algebraMap R S π) q ≠ 0
    rw [tensorEquivLocalCompletions_one_tmul]
    exact branchCompletion_uniformizer_ne_zero R S hπ q
  have hcu (q) : ¬ IsUnit (c q) := by
    change ¬ IsUnit (tensorEquivLocalCompletions (maximalIdeal R) hI
      (1 ⊗ₜ[R] algebraMap R S π) q)
    rw [tensorEquivLocalCompletions_one_tmul]
    exact branchCompletion_uniformizer_not_isUnit R S hπ q
  letI := IsDiscreteValuationRing.isLocalizationAway_of_finite (S := S) E hπ
  exact (IsLocalization.Away.tensorProductEquivTMulRight R
    (AdicCompletion (maximalIdeal R) R) (algebraMap R S π) E).trans
      ((IsLocalization.algEquivOfAlgEquiv
        (M := Submonoid.powers
          ((1 : AdicCompletion (maximalIdeal R) R) ⊗ₜ[R] algebraMap R S π))
        (T := Submonoid.powers c)
        (Localization.Away ((1 : AdicCompletion (maximalIdeal R) R) ⊗ₜ[R] algebraMap R S π))
        (Localization.Away c) ε (by simp only [Submonoid.map_powers]; rfl)).trans
          (IsDiscreteValuationRing.fractionPiAwayAlgEquiv D c hc hcu
            (AdicCompletion (maximalIdeal R) R)))

/-- Original integral elements enter each field by the native localized completion map. -/
@[simp] theorem tensorEquivLocalFractionFields_one_tmul
    (hI : (maximalIdeal R).map (algebraMap R S) ≠ 0)
    {π : R} (hπ : Irreducible π) (s : S)
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := fun q ↦ localCompletionBaseAlgebra (maximalIdeal R) hI q
    tensorEquivLocalFractionFields R S E hI hπ (1 ⊗ₜ[R] algebraMap S E s) q =
      algebraMap (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
        (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))
        (algebraMap S (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) s) := by
  let := fun q ↦ localCompletionBaseAlgebra (maximalIdeal R) hI q
  simp only [tensorEquivLocalFractionFields, AlgEquiv.trans_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul,
    IsLocalization.algEquivOfAlgEquiv_eq,
    IsDiscreteValuationRing.fractionPiAwayAlgEquiv_algebraMap]
  change algebraMap _ _ (tensorEquivLocalCompletions (maximalIdeal R) hI (1 ⊗ₜ[R] s) q) = _
  rw [tensorEquivLocalCompletions_one_tmul]
  rfl

end AdicCompletion
