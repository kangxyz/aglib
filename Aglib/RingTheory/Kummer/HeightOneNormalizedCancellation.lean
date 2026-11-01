/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.NormalizedHeightOne
public import Aglib.RingTheory.Kummer.DVRRootCancellationCanonical
public import Aglib.RingTheory.IntegralClosure.LocalizationUnramified
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Cancellation at the specified height-one normalization prime

The original generic fields and the original normalization prime are retained.
The coefficient localization at the parameter prime is a DVR, and its root
algebra is the localization at the proved contraction of that same prime.
DVR cancellation and native integral-closure localization then prove formal
unramifiedness of the original source localization.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace Algebra.Kummer

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
  [IsRegularLocalRing (R ⧸ Ideal.span {f})]
  (N : ℕ) (hN : 0 < N) (hreg : IsSMulRegular R f)

local notation "T" => RootAlgebra N f
local notation "P" => (Ideal.span {(f : R)} : Ideal R)
local notation "J" => (Ideal.span {AdjoinRoot.root (rootPolynomial N f)} : Ideal T)
local notation "D₀" => Localization.AtPrime P
local notation "D" => RootAlgebra N (algebraMap R D₀ f)

local instance : (P).IsPrime := regularParameter_span_isPrime R f

variable (K F L : Type u)
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field F] [Algebra R F] [Algebra (RootAlgebra N f) F]
  [IsScalarTower R (RootAlgebra N f) F] [IsFractionRing (RootAlgebra N f) F]
  [Algebra K F] [IsScalarTower R K F]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]


variable (Ω : Type u) [Field Ω]
  [Algebra (Localization.AtPrime (Ideal.span {f} : Ideal R)) Ω]
  [IsLocalHom (algebraMap (Localization.AtPrime (Ideal.span {f} : Ideal R)) Ω)]
  [IsSepClosed Ω]

include hf hN hreg Ω in
/-- Bounded cancellation proves formal unramifiedness at the specified
height-one source prime above the root divisor. Neither domain nor integrality
of the localized source over the original base is assumed. -/
theorem parameterRoot_normalization_formallyUnramified_at_heightOne
    (hunit : IsUnit (N : R)) (hcard : Nat.card (L ≃ₐ[K] L) ∣ N)
    (q : Ideal (integralClosure T (F ⊗[K] L))) [q.IsPrime] (hq : q.height = 1)
    (hdiv : algebraMap T (integralClosure T (F ⊗[K] L))
      (AdjoinRoot.root (rootPolynomial N f)) ∈ q) :
    Algebra.FormallyUnramified T (Localization.AtPrime q) := by
  let : IsRegularLocalRing R :=
    IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : (J).IsPrime :=
    (Ideal.span_singleton_prime (parameterRoot_root_prime R f hf N hN hreg).ne_zero).mpr
      (parameterRoot_root_prime R f hf N hN hreg)
  let : Algebra T D := rootBaseChangeAlgebra D₀ N f
  let : IsScalarTower R T D :=
    IsScalarTower.of_algebraMap_eq fun r => ((rootBaseChangeHom D₀ N f).commutes r).symm
  let : IsLocalization.AtPrime D J :=
    parameterLocalizedRoot_isLocalizationAtPrime N f hN
  let : Algebra D₀ K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe D₀ K (P).primeCompl R⁰
      (P).primeCompl_le_nonZeroDivisors
  let : IsScalarTower R D₀ K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D₀ K (P).primeCompl R⁰
      (P).primeCompl_le_nonZeroDivisors
  let : IsFractionRing D₀ K :=
    IsFractionRing.isFractionRing_of_isLocalization (P).primeCompl D₀ K
      (P).primeCompl_le_nonZeroDivisors
  let : Algebra D₀ F :=
    ((algebraMap K F).comp (algebraMap D₀ K)).toAlgebra
  let : IsScalarTower D₀ K F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R D₀ F := IsScalarTower.to₁₂₄ R D₀ K F
  let : Algebra D F :=
    IsLocalization.localizationAlgebraOfSubmonoidLe D F (J).primeCompl T⁰
      (J).primeCompl_le_nonZeroDivisors
  let : IsScalarTower T D F :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D F (J).primeCompl T⁰
      (J).primeCompl_le_nonZeroDivisors
  let : IsScalarTower R D F := IsScalarTower.to₁₃₄ R T D F
  let : IsScalarTower D₀ D F := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (P).primeCompl
    ext r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  let : IsFractionRing D F :=
    IsFractionRing.isFractionRing_of_isLocalization (J).primeCompl D F
      (J).primeCompl_le_nonZeroDivisors
  let : Algebra.Etale K L := by
    let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    let : Algebra.FinitePresentation K L :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact ⟨inferInstance, inferInstance⟩
  let : IsDiscreteValuationRing D₀ := parameterPrime_isDiscreteValuationRing R f hreg
  have hirr := parameterPrime_irreducible R f hreg
  have hunit' : IsUnit (N : D₀) := by
    simpa only [map_natCast] using hunit.map (algebraMap R D₀)
  let : Algebra.Etale D (integralClosure D (F ⊗[K] L)) :=
    dvrRoot_normalTensor_etale_of_geometricPoint D₀ Ω N (algebraMap R D₀ f)
      K F L hN hirr hunit' hcard
  let : IsLocalization.AtPrime D (q.under T) :=
    normalized_parameterRoot_isLocalizationAtPrime R f hf N hN hreg F (F ⊗[K] L) q hq hdiv
  exact integralClosure.formallyUnramified_atPrime_of_localized T D (F ⊗[K] L) q

end Algebra.Kummer
