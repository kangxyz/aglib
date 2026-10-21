/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismHartogs
public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismLocalEtale
public import Aglib.RingTheory.IntegralClosure.Inertia.NormalClosure
public import Aglib.RingTheory.IntegralClosure.LocalizedGenericFiber
public import Aglib.RingTheory.IntegralClosure.LocalizationTensor
public import Aglib.RingTheory.Etale.CodimensionOne

/-!
# Global Galois coefficient reconstruction from source codimension one

Unramifiedness at height-one primes of the original normalization supplies an
actual finite-etale model at each height-one base localization. Inertia then
makes the normal-closure normalization etale there. The canonical local Galois
maps and reflexive reconstruction yield the global coefficient equivalence.
No global freeness or Auslander theorem is assumed or concluded.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace integralClosure

variable (A K E Ω : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [Field Ω] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsGalois K Ω]

local notation "N" => IntermediateField.normalClosure K E Ω


/-- The actual base-localized normal-closure tensor algebra is etale at each
height-one base prime, derived from source-codimension-one unramifiedness. -/
theorem normalClosure_etale_atPrime_tensor_of_source_height_one
    (h : ∀ q : PrimeSpectrum (integralClosure A E), q.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt A q.asIdeal)
    (p : Ideal A) [p.IsPrime] (hh : p.height = 1) :
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[A] integralClosure A N) := by
  let : Module.Finite A (integralClosure A E) := IsIntegralClosure.finite A K E _
  let : FaithfulSMul A (integralClosure A E) :=
    (faithfulSMul_iff_algebraMap_injective A (integralClosure A E)).mpr (by
      intro x y hxy
      apply IsFractionRing.injective A K
      apply (algebraMap K E).injective
      have hh := congrArg (algebraMap (integralClosure A E) E) hxy
      simpa only [← IsScalarTower.algebraMap_apply] using hh)
  let D := Localization.AtPrime p
  let : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one p D hh
  let := IsLocalization.localizationAlgebraOfSubmonoidLe D K p.primeCompl A⁰
    p.primeCompl_le_nonZeroDivisors
  let : IsScalarTower A D K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D K p.primeCompl A⁰
      p.primeCompl_le_nonZeroDivisors
  let : IsFractionRing D K :=
    IsFractionRing.isFractionRing_of_isLocalization p.primeCompl D K
      p.primeCompl_le_nonZeroDivisors
  let : Algebra D Ω := ((algebraMap K Ω).comp (algebraMap D K)).toAlgebra
  let : IsScalarTower D K Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A D Ω := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A Ω a = algebraMap K Ω (algebraMap D K (algebraMap A D a))
    rw [← IsScalarTower.algebraMap_apply A D K, ← IsScalarTower.algebraMap_apply A K Ω]
  let : IsScalarTower D N Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A D N := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    change algebraMap A Ω a = algebraMap D Ω (algebraMap A D a)
    exact IsScalarTower.algebraMap_apply A D Ω a
  let : FaithfulSMul D (integralClosure D Ω) :=
    (faithfulSMul_iff_algebraMap_injective D (integralClosure D Ω)).mpr (by
      intro x y hxy
      apply IsFractionRing.injective D K
      apply (algebraMap K Ω).injective
      have heq := congrArg (algebraMap (integralClosure D Ω) Ω) hxy
      simpa only [← IsScalarTower.algebraMap_apply] using heq)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure D Ω) (IsLocalRing.maximalIdeal D)
  let := hQ
  let := hQP
  let : Algebra.Etale D (D ⊗[A] integralClosure A E) :=
    Algebra.etale_atPrime_tensor_of_height_one h p hh
  let : Algebra.Etale D (integralClosure D N) :=
    Inertia.normalClosure_etale_of_finiteEtaleModel D K Ω (D ⊗[A] integralClosure A E) E
      (localizedGenericFiberEquiv A K E D) Q
  exact Algebra.Etale.of_equiv (scalarExtensionTensorEquiv A D N p.primeCompl).symm

/-- Source-codimension-one unramifiedness reconstructs the original coefficient
map for the literal normalization in the actual normal closure. -/
theorem normalClosure_galoisEndomorphism_surjective
    (h : ∀ q : PrimeSpectrum (integralClosure A E), q.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt A q.asIdeal) :
    Function.Surjective (IsIntegralClosure.galoisEndomorphism A K N (integralClosure A N)) := by
  apply IsIntegralClosure.galoisEndomorphism_surjective_of_localized_height_one
    A K N (integralClosure A N)
  intro p hp hh
  let D := Localization.AtPrime p
  let : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one p D hh
  let := IsLocalization.localizationAlgebraOfSubmonoidLe D K p.primeCompl A⁰
    p.primeCompl_le_nonZeroDivisors
  let : IsScalarTower A D K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D K p.primeCompl A⁰
      p.primeCompl_le_nonZeroDivisors
  let : IsFractionRing D K :=
    IsFractionRing.isFractionRing_of_isLocalization p.primeCompl D K
      p.primeCompl_le_nonZeroDivisors
  let : Algebra D Ω := ((algebraMap K Ω).comp (algebraMap D K)).toAlgebra
  let : IsScalarTower D K Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A D Ω := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A Ω a = algebraMap K Ω (algebraMap D K (algebraMap A D a))
    rw [← IsScalarTower.algebraMap_apply A D K, ← IsScalarTower.algebraMap_apply A K Ω]
  let : IsScalarTower D N Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A D N := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    change algebraMap A Ω a = algebraMap D Ω (algebraMap A D a)
    exact IsScalarTower.algebraMap_apply A D Ω a
  let : Algebra.Etale D (D ⊗[A] integralClosure A N) :=
    normalClosure_etale_atPrime_tensor_of_source_height_one A K E Ω h p hh
  let : Algebra.Etale D (integralClosure D N) :=
    Algebra.Etale.of_equiv (scalarExtensionTensorEquiv A D N p.primeCompl)
  exact galoisEndomorphism_localized_surjective_of_etale A K N D p.primeCompl

/-- The original coefficient map is an equivalence; the conclusion does not
assert that the normalization is globally free or already etale. -/
def normalClosureGaloisEndomorphismEquiv
    (h : ∀ q : PrimeSpectrum (integralClosure A E), q.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt A q.asIdeal) :
    ((N ≃ₐ[K] N) → integralClosure A N) ≃ₗ[integralClosure A N]
      Module.End A (integralClosure A N) :=
  LinearEquiv.ofBijective (IsIntegralClosure.galoisEndomorphism A K N (integralClosure A N))
    ⟨IsIntegralClosure.galoisEndomorphism_injective A K N (integralClosure A N),
      normalClosure_galoisEndomorphism_surjective A K E Ω h⟩

end integralClosure
