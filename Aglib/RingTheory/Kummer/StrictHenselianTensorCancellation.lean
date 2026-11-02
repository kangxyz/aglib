/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.BoundedRootCancellation
public import Aglib.RingTheory.IntegralClosure.FiniteEtale.GenericBaseChange
public import Aglib.RingTheory.IntegralClosure.FiniteEtale.LocalFactorGaloisBaseChange

/-! # Bounded root cancellation for the original base-changed Galois algebra

The original coefficient extension may disconnect the Galois algebra. Its
actual normalization primes supply all the literal generic field factors.
Their inherited Galois bounds give component cancellation, and the canonical
finite product comparison proves etaleness of the unchanged normalization.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.Kummer

section CompatibleAction

variable (R K L F : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [IsGalois K L]
  (π : R) (hπ : Irreducible π) (N : ℕ) (hN : 0 < N)
  (hunit : IsUnit (N : R)) (hcard : Nat.card (L ≃ₐ[K] L) ∣ N)
  [Field F] [Algebra R F] [Algebra K F] [IsScalarTower R K F]
  [Algebra (RootAlgebra N π) F] [IsScalarTower R (RootAlgebra N π) F]
  [IsFractionRing (RootAlgebra N π) F] [FaithfulSMul R F]

include hπ hN hunit hcard

/-- Bounded cancellation retains any supplied compatible coefficient-field
action: uniqueness of the fraction lift identifies it with the constructed action. -/
theorem boundedRoot_normalTensor_etale_of_tower :
    Algebra.Etale (RootAlgebra N π)
      (integralClosure (RootAlgebra N π) (F ⊗[K] L)) := by
  have he : (rootChartCoefficientHom (R := R) K F).toRingHom = algebraMap K F := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    exact (rootChartCoefficientHom (R := R) K F).commutes r |>.trans
      (IsScalarTower.algebraMap_apply R K F r)
  let σ : L →+* F := by
    letI : Algebra K F := (rootChartCoefficientHom (R := R) K F).toRingHom.toAlgebra
    exact (boundedRootFieldHom (R := R) (K := K) (L := L) (π := π)
      (hπ := hπ) (N := N) (hunit := hunit) (hcard := hcard) (F := F)).toRingHom
  have hc (k : K) : σ (algebraMap K L k) = rootChartCoefficientHom (R := R) K F k := by
    let : Algebra K F := (rootChartCoefficientHom (R := R) K F).toRingHom.toAlgebra
    exact (boundedRootFieldHom (R := R) (K := K) (L := L) (π := π)
      (hπ := hπ) (N := N) (hunit := hunit) (hcard := hcard) (F := F)).commutes k
  exact uniformizerRoot_normalTensor_etale R π hπ N hN K L F
    { σ with commutes' := fun k => (hc k).trans (RingHom.congr_fun he k) }

end CompatibleAction

section Product

variable (R K F A : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field F] [Algebra R F] [Algebra K F] [IsScalarTower R K F]
  [CommRing A] [Algebra K A]
  (π : R) (hπ : Irreducible π) (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : R))
  [Algebra (RootAlgebra N π) F] [IsScalarTower R (RootAlgebra N π) F]
  [IsFractionRing (RootAlgebra N π) F] [FaithfulSMul R F]
  {ι : Type*} [Finite ι] (M : ι → Type*)
  [∀ i, Field (M i)] [∀ i, Algebra K (M i)] [∀ i, Algebra R (M i)]
  [∀ i, IsScalarTower R K (M i)] [∀ i, FiniteDimensional K (M i)]
  [∀ i, IsGalois K (M i)]

include hπ hN hunit

/-- Assemble bounded cancellation through an actual finite field decomposition.
The complete normalization construction is performed before specialization to
literal localization fields, retaining their original algebra dictionaries. -/
theorem boundedRoot_normalTensor_etale_of_product
    (e : A ≃ₐ[K] ∀ i, M i) (hcard : ∀ i, Nat.card (M i ≃ₐ[K] M i) ∣ N) :
    Algebra.Etale (RootAlgebra N π)
      (integralClosure (RootAlgebra N π) (F ⊗[K] A)) := by
  classical
  let : IsDomain (RootAlgebra N π) := uniformizerRoot_isDomain R π hπ N hN
  let : IsDiscreteValuationRing (RootAlgebra N π) :=
    uniformizerRoot_isDiscreteValuationRing R π hπ N hN
  let (i : ι) : Algebra.Etale K (M i) := by
    let : Algebra.FormallyEtale K (M i) := Algebra.FormallyEtale.of_isSeparable K (M i)
    let : Algebra.FinitePresentation K (M i) :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact ⟨inferInstance, inferInstance⟩
  let (i : ι) : Module.Finite (RootAlgebra N π)
      (integralClosure (RootAlgebra N π) (F ⊗[K] M i)) :=
    integralClosure.finite_of_etale (RootAlgebra N π) F (F ⊗[K] M i)
  let (i : ι) : Algebra.Etale (RootAlgebra N π)
      (integralClosure (RootAlgebra N π) (F ⊗[K] M i)) :=
    boundedRoot_normalTensor_etale_of_tower R K (M i) F π hπ N hN hunit (hcard i)
  let : Fintype ι := Fintype.ofFinite ι
  let eF := (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) e).trans
    (Algebra.TensorProduct.piRight K F F M)
  exact Algebra.Etale.of_equiv
    (integralClosure.equivPi (RootAlgebra N π) (F ⊗[K] A) (fun i => F ⊗[K] M i)
      (eF.restrictScalars (RootAlgebra N π))).symm

end Product

section OriginalTensor

variable (R K L K' : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Field K'] [Algebra K K'] [Algebra R K'] [IsFractionRing R K']
  (π : R) (hπ : Irreducible π) (N : ℕ) (hN : 0 < N)
  (hunit : IsUnit (N : R)) (hcard : Nat.card (L ≃ₐ[K] L) ∣ N)
  (F : Type*) [Field F] [Algebra R F] [Algebra K' F] [IsScalarTower R K' F]
  [Algebra (RootAlgebra N π) F] [IsScalarTower R (RootAlgebra N π) F]
  [IsFractionRing (RootAlgebra N π) F] [FaithfulSMul R F]

include hπ hN hunit hcard

/-- The unchanged normalization of the full original base-changed generic
algebra is etale, even when that generic algebra is disconnected. -/
theorem strictHenselian_normalBaseChangeTensor_etale :
    Algebra.Etale (RootAlgebra N π)
      (integralClosure (RootAlgebra N π) (F ⊗[K'] (K' ⊗[K] L))) := by
  let : Algebra.Etale K L := by
    let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    let : Algebra.FinitePresentation K L :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact ⟨inferInstance, inferInstance⟩
  let A := K' ⊗[K] L
  let B := integralClosure R A
  let M := fun q : MaximalSpectrum B => K' ⊗[R] Localization.AtPrime q.asIdeal
  let : Finite (MaximalSpectrum B) := integralClosure.LocalFactor.finite_maximalSpectrum R K' A
  let (q : MaximalSpectrum B) : Field (M q) :=
    integralClosure.LocalFactor.genericField R K' A q.asIdeal
  let (q : MaximalSpectrum B) : Module.Finite K' (M q) :=
    integralClosure.LocalFactor.generic_finite R K' A q.asIdeal
  have hg (q : MaximalSpectrum B) :=
    integralClosure.LocalFactor.baseChange_genericField_isGalois_and_card_dvd R K L K' q.asIdeal
  let (q : MaximalSpectrum B) : IsGalois K' (M q) := (hg q).1
  exact boundedRoot_normalTensor_etale_of_product R K' F A π hπ N hN hunit M
    (integralClosure.LocalFactor.genericDecomposition R K' A)
    (fun q => (hg q).2.trans hcard)

end OriginalTensor

end Algebra.Kummer
