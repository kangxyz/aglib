/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.CompletionBranch
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.ProductBaseChange
public import Aglib.RingTheory.AdicCompletion.FractionTensorBranches
public import Aglib.RingTheory.AdicCompletion.BranchFractionFinite
public import Aglib.RingTheory.AdicCompletion.OriginalBranchFractions

/-!
# Norm and residue over all original branches of a finite Dedekind model

Completion is used only in the proof. The conclusion retains the original
fraction field and every original localized valuation ring.
-/

@[expose] public noncomputable section


namespace MilnorK

open IsLocalRing AdicCompletion
open scoped TensorProduct

universe u
variable (R S F E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E] [FiniteDimensional F E]

/-- The actual finite norm commutes with the sum of residues at all original branches. -/
theorem residue_finiteExtensionNorm_dvr (n : ℕ) (x : K E (n + 1)) :
    letI := fun q : IdealBranch ((maximalIdeal R).map (algebraMap R S)) =>
      originalBranchFractionAlgebra S E q
    letI := fun q : IdealBranch ((maximalIdeal R).map (algebraMap R S)) =>
      originalBranchIsFractionRing S E q
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      ∑ q : IdealBranch ((maximalIdeal R).map (algebraMap R S)),
        finiteExtensionNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) n
          (DVR.residue (Localization.AtPrime q.val) E n x) := by
  let := fun q : IdealBranch ((maximalIdeal R).map (algebraMap R S)) =>
    originalBranchFractionAlgebra S E q
  let := fun q : IdealBranch ((maximalIdeal R).map (algebraMap R S)) =>
    originalBranchIsFractionRing S E q
  let := fun q : IdealBranch ((maximalIdeal R).map (algebraMap R S)) =>
    originalBranchFractionTower S E q
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm : maximalIdeal R ≠ 0 := by
    intro h
    have hp : π ∈ maximalIdeal R := (mem_maximalIdeal π).mpr hπ.not_isUnit
    rw [h] at hp
    exact hπ.ne_zero hp
  have hI : (maximalIdeal R).map (algebraMap R S) ≠ 0 :=
    Ideal.map_ne_bot_of_ne_bot hm
  let T := AdicCompletion (maximalIdeal R) R
  let L := FractionRing T
  let J := (maximalIdeal R).map (algebraMap R S)
  let D := fun q : IdealBranch J => FractionRing (BranchCompletion J q)
  let := fractionCompletionAlgebra R F
  let := fun q => localCompletionBaseAlgebra (maximalIdeal R) hI q
  let := fun q => localCompletionBaseFinite (maximalIdeal R) hI q
  let := fun q => localCompletionBaseIsScalarTower (maximalIdeal R) hI q
  let := fun q => localCompletionBase_isLocalHom R S hI q
  let := fun q => localCompletionFractionAlgebra R S hI q
  let := fun q => localCompletionFractionIsScalarTower R S hI q
  let := fun q => localCompletionFractionFinite R S hI q
  let : CharZero T := RingHom.charZero
    ((AdicCompletion.residueFieldEquiv R).toRingHom.comp (IsLocalRing.residue T))
  let : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective T L)
  let e := fractionTensorEquivLocalFractionFields R S F E hI hπ
  rw [← DVR.residue_completion_identification R F]
  change map n (AdicCompletion.residueFieldEquiv R).toRingHom
    (DVR.residue T L n (map (n + 1) (algebraMap F L)
      (finiteExtensionNorm F E (n + 1) x))) = _
  rw [finiteExtensionNorm_restrict_tensorProduct D E e, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hc : ((Pi.evalRingHom D q).comp e.toRingHom).comp
      Algebra.TensorProduct.includeRight.toRingHom =
        AdicCompletion.fractionRingMap (Localization.AtPrime q.val) E := by
    apply IsFractionRing.ringHom_ext (A := S)
    intro s
    simp only [RingHom.comp_apply, Pi.evalRingHom_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply]
    rw [fractionTensorEquivLocalFractionFields_one_tmul]
    rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime q.val) E]
    rw [AdicCompletion.fractionRingMap_algebraMap]
    rfl
  rw [hc]
  exact residue_completed_norm_eq_original_branch R (Localization.AtPrime q.val) E n x

end MilnorK
