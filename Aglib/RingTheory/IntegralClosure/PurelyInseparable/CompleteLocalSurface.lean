/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.HeightOne
public import Aglib.RingTheory.IntegralClosure.HeightOneLocalization
public import Aglib.RingTheory.IntegralClosure.PurelyInseparable.FiniteGeneration
public import Aglib.RingTheory.IntegralClosure.PurelyInseparable.ResidueLayers
public import Aglib.RingTheory.IntegralClosure.PurelyInseparable.HeightOneResidues
public import Aglib.RingTheory.Localization.HeightOne
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Tactic.NormNum

/-! # The original complete normal surface specialization -/
@[expose] public noncomputable section
open scoped Pointwise nonZeroDivisors
namespace integralClosure
attribute [local instance] heightOneAtPrimeAlgebra heightOneAtPrimeFractionAlgebra

private theorem primeQuotient_dimLE_one (R : Type*) [CommRing R] [IsDomain R]
    [Ring.KrullDimLE 2 R] (p : Ideal R)
    (x : R) (hx : x ≠ 0) (hxp : x ∈ p) : Ring.KrullDimLE 1 (R ⧸ p) := by
  apply Ring.krullDimLE_iff.mpr
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  have hdim := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hxp)
  convert hdim.trans
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 R)) using 1
  norm_num

section Complete

variable (R K E : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [IsLocalRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Ring.KrullDimLE 2 R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field E] [Algebra R E] [Algebra K E] [IsScalarTower R K E]
  [FiniteDimensional K E] [IsPurelyInseparable K E]

local notation "S" => integralClosure R E

include K

private theorem heightOneResidueNormalizationFinite_of_dimLE_two [FaithfulSMul R E] :
    HeightOneResidueNormalizationFinite R K E := by
  intro p hp hheight
  let : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one p
      (Localization.AtPrime p) hheight
  let : IsDiscreteValuationRing (integralClosure (Localization.AtPrime p) E) :=
    isDiscreteValuationRing_of_isPurelyInseparable (Localization.AtPrime p) K E
  let : IsLocalHom (algebraMap (Localization.AtPrime p)
      (integralClosure (Localization.AtPrime p) E)) :=
    algebraMap_isLocalHom (Localization.AtPrime p) K E
  let _ := atPrimeResidueQuotientAlgebra p E
  obtain ⟨x, hxp, hx⟩ := p.ne_bot_iff.mp (Ideal.ne_bot_of_height_eq_one hheight)
  let : Ring.KrullDimLE 1 (R ⧸ p) := primeQuotient_dimLE_one R p x hx hxp
  let : Module.Finite R
      (integralClosure (R ⧸ p)
        (IsLocalRing.ResidueField (integralClosure (Localization.AtPrime p) E))) :=
    finite_atPrimeResidueNormalization p K E
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ p) _

/-- The original surface scalar quotient, supplied by the actual complete curve residues. -/
theorem finite_scalar_quotient_of_complete_local_normal_dimLE_two
    (x : R) (hx : x ≠ 0) : Module.Finite R (QuotSMulTop x S) := by
  let : Module.IsTorsionFree R E := .trans_faithfulSMul R K E
  exact finite_scalar_quotient_of_finite_heightOneResidueNormalization R K E
    (heightOneResidueNormalizationFinite_of_dimLE_two R K E) x hx

/-- The original surface normalization, with unchanged fields and coefficient maps. -/
theorem finite_of_complete_local_normal_dimLE_two_of_isPurelyInseparable :
    Module.Finite R S := by
  let : Module.IsTorsionFree R E := .trans_faithfulSMul R K E
  exact finite_of_complete_local_normal_of_finite_heightOneResidueNormalization R K E
    (heightOneResidueNormalizationFinite_of_dimLE_two R K E)

end Complete
end integralClosure
