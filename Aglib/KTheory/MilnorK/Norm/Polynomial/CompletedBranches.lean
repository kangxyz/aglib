/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.Complete
public import Aglib.KTheory.MilnorK.Residue.AdicCompletion

/-!
# Norm residue as the full completed branch sum

The original noncomplete DVR residue is expressed using every actual factor
over the completed fraction field. This is not yet an identification with the
closed points of an original curve: that requires the finite closure completion
comparison. No such comparison is assumed here.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial PolynomialResidue Polynomial.LocalResidue AdjoinRoot IsLocalRing
open IsDiscreteValuationRing.CompleteExtension

universe u

/-- The actual residue norm for a root field over a complete DVR. -/
def completeBranchResidueNorm
    (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    (p : MonicIrreducible F) (n : ℕ) : K (AdjoinRoot p.val) (n + 1) →ₗ[ℤ]
      K (ResidueField R) n := by
  let _ := p.property.1.finite_adjoinRoot
  let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot p.val)
  let _ := integralClosure_isLocalHom R F (AdjoinRoot p.val)
  let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot p.val)
    (integralClosure R (AdjoinRoot p.val))
  let _ := integralClosure_residue_finite R F (AdjoinRoot p.val)
  exact (finiteExtensionNorm (ResidueField R)
    (ResidueField (integralClosure R (AdjoinRoot p.val))) n).comp
      (DVR.residue (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) n)

/-- The norm of the actual completed residue computes its branch contribution. -/
theorem completeBranchResidueNorm_eq
    (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    (p : MonicIrreducible F) (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    completeBranchResidueNorm R F p n x =
      DVR.residue R F n (polynomialNorm (n + 1) p x) :=
  (residue_polynomialNorm_complete R F p n x).symm

variable (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)] [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]

local instance completionResidueCharZero :
    CharZero (ResidueField (AdicCompletion (maximalIdeal R) R)) :=
  charZero_of_injective_ringHom (AdicCompletion.residueFieldEquiv R).symm.injective

local instance completionFractionCharZero :
    CharZero (FractionRing (AdicCompletion (maximalIdeal R) R)) := by
  let : CharZero (AdicCompletion (maximalIdeal R) R) :=
    RingHom.charZero (IsLocalRing.residue (AdicCompletion (maximalIdeal R) R))
  exact charZero_of_injective_algebraMap
    (IsFractionRing.injective (AdicCompletion (maximalIdeal R) R) _)

/-- Full factor sum over the completed fraction field, retaining the literal
original coefficient/root maps and the canonical residue identification. -/
theorem residue_polynomialNorm_eq_completed_branch_sum
    (p : MonicIrreducible F) (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    DVR.residue R F n (polynomialNorm (n + 1) p x) =
      map n (AdicCompletion.residueFieldEquiv R).toRingHom
        (∑ q ∈ (placesAbove (AdicCompletion.fractionRingMap R F) p).attach,
          completeBranchResidueNorm (AdicCompletion (maximalIdeal R) R)
            (FractionRing (AdicCompletion (maximalIdeal R) R)) q.val n
              (map (n + 1) (adjoinRootMap (AdicCompletion.fractionRingMap R F)
                p.val q.val.val ((mem_placesAbove _ _ _).mp q.property)) x)) := by
  rw [← DVR.residue_completion_identification R F n
    (polynomialNorm (n + 1) p x)]
  apply congrArg
  rw [polynomialNorm_restrict, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact (completeBranchResidueNorm_eq _ _ q.val n _).symm

/-- The same full completed branch formula on an arbitrary original finite
extension, with the chosen presentation equivalence explicitly retained. -/
theorem residue_finiteExtensionNorm_eq_completed_branch_sum
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : MonicIrreducible F) (ε : AdjoinRoot p.val ≃ₐ[F] E)
    (n : ℕ) (x : K E (n + 1)) :
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      map n (AdicCompletion.residueFieldEquiv R).toRingHom
        (∑ q ∈ (placesAbove (AdicCompletion.fractionRingMap R F) p).attach,
          completeBranchResidueNorm (AdicCompletion (maximalIdeal R) R)
            (FractionRing (AdicCompletion (maximalIdeal R) R)) q.val n
              (map (n + 1) ((adjoinRootMap (AdicCompletion.fractionRingMap R F)
                p.val q.val.val ((mem_placesAbove _ _ _).mp q.property)).comp
                  ε.symm.toRingHom) x)) := by
  rw [finiteExtensionNorm_eq_presentation F E (n + 1) p ε, LinearMap.comp_apply,
    residue_polynomialNorm_eq_completed_branch_sum]
  apply congrArg
  apply Finset.sum_congr rfl
  intro q _
  rw [map_comp, LinearMap.comp_apply]

end MilnorK.PolynomialNorm
