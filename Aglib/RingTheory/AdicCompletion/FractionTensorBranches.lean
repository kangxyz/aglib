/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FractionBaseChange
public import Aglib.RingTheory.AdicCompletion.FractionBranches
public import Aglib.RingTheory.AdicCompletion.BranchFractionAlgebra

/-!
# Actual completed fraction tensor product over every original branch

The final equivalence is over the completed fraction field, using only its universal fraction
maps into each completed branch fraction field. Scalar compatibility follows from localization
uniqueness, not from an extra compatibility assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace AdicCompletion

open IsLocalRing
open scoped TensorProduct

universe u
variable (R S F E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E]

/-- The actual completed fraction tensor product splits over every original local branch. -/
def fractionTensorEquivLocalFractionFields
    (hI : (maximalIdeal R).map (algebraMap R S) ≠ 0) {π : R} (hπ : Irreducible π) :
    letI := fractionCompletionAlgebra R F
    letI := fun q ↦ localCompletionBaseAlgebra (maximalIdeal R) hI q
    letI := fun q ↦ localCompletionFractionAlgebra R S hI q
    FractionRing (AdicCompletion (maximalIdeal R) R) ⊗[F] E
      ≃ₐ[FractionRing (AdicCompletion (maximalIdeal R) R)]
        ∀ q : IdealBranch ((maximalIdeal R).map (algebraMap R S)),
          FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) := by
  letI := fractionCompletionAlgebra R F
  letI := fun q ↦ localCompletionBaseAlgebra (maximalIdeal R) hI q
  letI := fun q ↦ localCompletionFractionAlgebra R S hI q
  letI := fun q ↦ localCompletionFractionIsScalarTower R S hI q
  let ε := (fractionCompletionBaseChangeAlgEquiv R F E).trans
    (tensorEquivLocalFractionFields R S E hI hπ)
  refine AlgEquiv.ofRingEquiv (f := ε.toRingEquiv) ?_
  have h : ε.toRingHom.comp
      (algebraMap (FractionRing (AdicCompletion (maximalIdeal R) R))
        (FractionRing (AdicCompletion (maximalIdeal R) R) ⊗[F] E)) =
      algebraMap (FractionRing (AdicCompletion (maximalIdeal R) R))
        (∀ q : IdealBranch ((maximalIdeal R).map (algebraMap R S)),
          FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (AdicCompletion (maximalIdeal R) R))
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact ε.commutes x
  exact fun x ↦ DFunLike.congr_fun h x

/-- The final field product carries integral elements through their native branch maps. -/
@[simp] theorem fractionTensorEquivLocalFractionFields_one_tmul
    (hI : (maximalIdeal R).map (algebraMap R S) ≠ 0) {π : R} (hπ : Irreducible π)
    (s : S) (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := fractionCompletionAlgebra R F
    letI := fun q ↦ localCompletionBaseAlgebra (maximalIdeal R) hI q
    letI := fun q ↦ localCompletionFractionAlgebra R S hI q
    fractionTensorEquivLocalFractionFields R S F E hI hπ (1 ⊗ₜ[F] algebraMap S E s) q =
      algebraMap (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
        (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))
        (algebraMap S (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) s) := by
  let := fractionCompletionAlgebra R F
  let := fun q ↦ localCompletionBaseAlgebra (maximalIdeal R) hI q
  let := fun q ↦ localCompletionFractionAlgebra R S hI q
  change tensorEquivLocalFractionFields R S E hI hπ
    (fractionCompletionBaseChangeAlgEquiv R F E (1 ⊗ₜ[F] algebraMap S E s)) q = _
  rw [fractionCompletionBaseChangeAlgEquiv_one_tmul]
  exact tensorEquivLocalFractionFields_one_tmul R S E hI hπ s q

end AdicCompletion
