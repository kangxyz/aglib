/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.PurelyInseparable.ResidueLayers.Core

/-! # Complete-curve supply for the original residue-layer construction -/

@[expose] public noncomputable section
open scoped Pointwise nonZeroDivisors
namespace integralClosure

section Complete

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [IsLocalRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  (p : Ideal R) [p.IsPrime] [Ring.KrullDimLE 1 (R ⧸ p)]
  [IsDiscreteValuationRing (Localization.AtPrime p)]
  (K E : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [Algebra (Localization.AtPrime p) K] [IsFractionRing (Localization.AtPrime p) K]
  [Field E] [Algebra R E] [Algebra K E] [IsScalarTower R K E]
  [Algebra (Localization.AtPrime p) E] [IsScalarTower R (Localization.AtPrime p) E]
  [IsScalarTower (Localization.AtPrime p) K E]
  [FiniteDimensional K E] [IsPurelyInseparable K E]

local notation "A" => Localization.AtPrime p
local notation "S" => integralClosure R E
local notation "T" => integralClosure A E
local notation "C" => R ⧸ p

local notation "ℓ" => IsLocalRing.ResidueField T

attribute [local instance] atPrimeResidueQuotientAlgebra

include K in
omit [IsIntegrallyClosed R] [Algebra R K] [IsFractionRing R K] [IsScalarTower R K E] in
/-- The normalization of the actual prime quotient in the actual local
residue field is finite over the original complete ring. -/
theorem finite_atPrimeResidueNormalization :
    let _ : IsDiscreteValuationRing T := isDiscreteValuationRing_of_isPurelyInseparable A K E
    let _ : IsLocalHom (algebraMap A T) := algebraMap_isLocalHom A K E
    Module.Finite R (integralClosure C ℓ) := by
  let : IsDiscreteValuationRing T := isDiscreteValuationRing_of_isPurelyInseparable A K E
  let : IsLocalHom (algebraMap A T) := algebraMap_isLocalHom A K E
  change Module.Finite R (integralClosure C ℓ)
  let : IsNoetherianRing C := isNoetherianRing_of_surjective R C
    (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : IsLocalRing C := IsLocalRing.of_surjective' (Ideal.Quotient.mk p)
    Ideal.Quotient.mk_surjective
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) C := by
    have h := IsAdicComplete.map_algebraMap_of_finite R (IsLocalRing.maximalIdeal R) C
    rwa [IsLocalRing.map_maximalIdeal_of_surjective
      (algebraMap R C) Ideal.Quotient.mk_surjective] at h
  let : Algebra p.ResidueField ℓ := purelyInseparableResidueAlgebra A K E
  let : IsScalarTower C p.ResidueField ℓ := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change algebraMap R ℓ r =
      algebraMap p.ResidueField ℓ (algebraMap R p.ResidueField r)
    exact IsScalarTower.algebraMap_apply R p.ResidueField ℓ r
  let : Module.Finite p.ResidueField ℓ := finite_residueField_of_isPurelyInseparable A K E
  let : Module.Finite C (integralClosure C ℓ) :=
    finite_of_complete_local_dimLE_one C p.ResidueField ℓ
  exact Module.Finite.trans C (integralClosure C ℓ)

include K in
/-- The original complete-curve instance of the dimension-free residue producer. -/
theorem finite_atPrimeOrder_layer (z : S)
    (hz : Irreducible (toAtPrimeNormalization p E z)) (j : ℕ) :
    Module.Finite R
      (atPrimeOrder p E z j ⧸ (atPrimeOrder p E z (j + 1)).comap
        (atPrimeOrder p E z j).subtype) := by
  let : IsDiscreteValuationRing T := isDiscreteValuationRing_of_isPurelyInseparable A K E
  let : IsLocalHom (algebraMap A T) := algebraMap_isLocalHom A K E
  let : Module.Finite R (integralClosure C ℓ) := finite_atPrimeResidueNormalization p K E
  have hres : Module.Finite C (integralClosure C ℓ) :=
    Module.Finite.of_restrictScalars_finite R C _
  exact finite_atPrimeOrder_layer_of_finite_residueNormalization p K E hres z hz j

include K in
/-- The original complete-curve instance of the dimension-free residue producer. -/
theorem finite_quotient_atPrimeOrder (z : S)
    (hz : Irreducible (toAtPrimeNormalization p E z)) (n : ℕ) :
    Module.Finite R (S ⧸ atPrimeOrder p E z n) := by
  let : IsDiscreteValuationRing T := isDiscreteValuationRing_of_isPurelyInseparable A K E
  let : IsLocalHom (algebraMap A T) := algebraMap_isLocalHom A K E
  let : Module.Finite R (integralClosure C ℓ) := finite_atPrimeResidueNormalization p K E
  have hres : Module.Finite C (integralClosure C ℓ) :=
    Module.Finite.of_restrictScalars_finite R C _
  exact finite_quotient_atPrimeOrder_of_finite_residueNormalization p K E hres z hz n

include K in
/-- The original complete-curve instance of the dimension-free residue producer. -/
theorem finite_range_toAtPrimeQuotient (t : T) (ht : t ≠ 0) :
    Module.Finite R (LinearMap.range (toAtPrimeQuotient p E t).toLinearMap) := by
  let : IsDiscreteValuationRing T := isDiscreteValuationRing_of_isPurelyInseparable A K E
  let : IsLocalHom (algebraMap A T) := algebraMap_isLocalHom A K E
  let : Module.Finite R (integralClosure C ℓ) := finite_atPrimeResidueNormalization p K E
  have hres : Module.Finite C (integralClosure C ℓ) :=
    Module.Finite.of_restrictScalars_finite R C _
  exact finite_range_toAtPrimeQuotient_of_finite_residueNormalization p K E hres t ht

include K in
/-- The original complete-curve instance of the dimension-free residue producer. -/
theorem finite_range_toAtPrimeQuotient_algebraMap (x : R) (hx : x ≠ 0) :
    Module.Finite R
      (LinearMap.range (toAtPrimeQuotient p E (algebraMap R T x)).toLinearMap) := by
  let : IsDiscreteValuationRing T := isDiscreteValuationRing_of_isPurelyInseparable A K E
  let : IsLocalHom (algebraMap A T) := algebraMap_isLocalHom A K E
  let : Module.Finite R (integralClosure C ℓ) := finite_atPrimeResidueNormalization p K E
  have hres : Module.Finite C (integralClosure C ℓ) :=
    Module.Finite.of_restrictScalars_finite R C _
  exact finite_range_toAtPrimeQuotient_algebraMap_of_finite_residueNormalization p K E hres x hx

end Complete

end integralClosure
