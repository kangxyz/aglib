/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.HeightOne
public import Aglib.RingTheory.IntegralClosure.HeightOneLocalization
public import Aglib.RingTheory.IntegralClosure.PurelyInseparable.FiniteGeneration
public import Aglib.RingTheory.IntegralClosure.PurelyInseparable.ResidueLayers.Core
public import Aglib.RingTheory.Localization.HeightOne
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Tactic.NormNum

/-!
# Purely inseparable normalization from actual height-one residues

The scalar quotient of the literal normalization embeds into the finite product
of its actual images in the local normalization quotients at the minimal primes
over the scalar. Height-one divisibility in the normal base identifies the
kernel. Coefficient lifting then proves finite normalization, without assuming
Noetherianity, completeness, or module finiteness of the normalization.
-/

@[expose] public noncomputable section

open scoped Pointwise nonZeroDivisors

namespace integralClosure

private def QuotientFinite {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (Q : Submodule R M) : Prop := Module.Finite R (M ⧸ Q)

private theorem quotientFinite_of_ker_eq {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsNoetherian R N] (f : M →ₗ[R] N) (Q : Submodule R M)
    (hker : LinearMap.ker f = Q) : QuotientFinite Q := by
  change Q.CoFG
  rw [← hker]
  exact Submodule.CoFG.ker f

private theorem finite_quotSMulTop_of_quotientFinite {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (x : R)
    (h : QuotientFinite (x • (⊤ : Submodule R M))) :
    Module.Finite R (QuotSMulTop x M) := by
  change QuotientFinite (x • (⊤ : Submodule R M))
  exact h

section LocalizationAlgebras

variable {R : Type*} [CommRing R]

/-- The localization action is the unique extension of the original faithful
coefficient map into the ambient field. -/
@[instance_reducible]
def heightOneAtPrimeAlgebra (E : Type*) [Field E] [Algebra R E]
    [FaithfulSMul R E] (p : Ideal R) [p.IsPrime] :
    Algebra (Localization.AtPrime p) E :=
  (IsLocalization.lift (S := Localization.AtPrime p) (g := algebraMap R E)
    (fun s : p.primeCompl ↦ isUnit_iff_ne_zero.mpr (by
      intro h
      have hs : (s : R) = 0 := (FaithfulSMul.algebraMap_injective R E)
        (by simpa only [map_zero] using h)
      exact s.property (hs.symm ▸ p.zero_mem)))).toAlgebra

attribute [local instance] heightOneAtPrimeAlgebra

instance heightOneAtPrimeBaseTower (E : Type*) [Field E] [Algebra R E]
    [FaithfulSMul R E] (p : Ideal R) [p.IsPrime] :
    IsScalarTower R (Localization.AtPrime p) E := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (IsLocalization.lift_comp _).symm

/-- The original fraction-field action of the prime localization. -/
@[instance_reducible]
def heightOneAtPrimeFractionAlgebra [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (p : Ideal R) [p.IsPrime] :
    Algebra (Localization.AtPrime p) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime p) K
    p.primeCompl R⁰ p.primeCompl_le_nonZeroDivisors

attribute [local instance] heightOneAtPrimeFractionAlgebra

instance heightOneAtPrimeFractionTower [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (p : Ideal R) [p.IsPrime] :
    IsScalarTower R (Localization.AtPrime p) K :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (Localization.AtPrime p) K p.primeCompl R⁰ p.primeCompl_le_nonZeroDivisors

instance heightOneAtPrimeIsFractionRing [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (p : Ideal R) [p.IsPrime] :
    IsFractionRing (Localization.AtPrime p) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    p.primeCompl (Localization.AtPrime p) K

instance heightOneAtPrimeFieldTower [IsDomain R] (K E : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] [Field E]
    [Algebra R E] [FaithfulSMul R E] [Algebra K E] [IsScalarTower R K E]
    (p : Ideal R) [p.IsPrime] : IsScalarTower (Localization.AtPrime p) K E := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext p.primeCompl
  ext r
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

end LocalizationAlgebras

attribute [local instance] heightOneAtPrimeAlgebra heightOneAtPrimeFractionAlgebra

section LocalImages

variable {R : Type*} [CommRing R] (E : Type*) [Field E] [Algebra R E]
  [FaithfulSMul R E]

private instance heightOneMinimalPrimeIsPrime (x : R)
    (p : (Ideal.span {x}).minimalPrimes) : p.val.IsPrime := p.property.isPrime

private def heightOneLocalQuotientMap (x : R) (p : (Ideal.span {x}).minimalPrimes) :
    integralClosure R E →ₗ[R]
      integralClosure (Localization.AtPrime p.val) E ⧸ Ideal.span
        {algebraMap R (integralClosure (Localization.AtPrime p.val) E) x} :=
  (toAtPrimeQuotient p.val E
    (algebraMap R (integralClosure (Localization.AtPrime p.val) E) x)).toLinearMap

private def heightOneLocalImages (x : R) : Type _ :=
  ∀ p : (Ideal.span {x}).minimalPrimes,
    LinearMap.range (heightOneLocalQuotientMap E x p)

private instance heightOneLocalImagesAddCommGroup (x : R) :
    AddCommGroup (heightOneLocalImages E x) :=
  inferInstanceAs (AddCommGroup
    (∀ p : (Ideal.span {x}).minimalPrimes,
      LinearMap.range (heightOneLocalQuotientMap E x p)))

private instance heightOneLocalImagesModule (x : R) :
    Module R (heightOneLocalImages E x) :=
  inferInstanceAs (Module R
    (∀ p : (Ideal.span {x}).minimalPrimes,
      LinearMap.range (heightOneLocalQuotientMap E x p)))

private def heightOneToLocalImages (x : R) :
    integralClosure R E →ₗ[R] heightOneLocalImages E x :=
  LinearMap.pi fun p ↦ (heightOneLocalQuotientMap E x p).rangeRestrict

end LocalImages

section Kernel

variable (R K E : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field E] [Algebra R E] [FaithfulSMul R E] [Algebra K E]
  [IsScalarTower R K E] [FiniteDimensional K E] [IsPurelyInseparable K E]

local notation "S" => integralClosure R E

include K

/-- Local divisibility over the height-one primes containing a nonzero
coefficient detects its scalar multiple submodule in the normalization.
The intersection theorem is applied only to the normal coefficient ring. -/
private theorem mem_scalar_smul_top_of_div_integral_at_height_one
    (x : R) (hx : x ≠ 0) (b : S)
    (hb : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → x ∈ p →
      (b : E) / algebraMap R E x ∈ integralClosure (Localization.AtPrime p) E) :
    b ∈ x • (⊤ : Submodule R S) := by
  obtain ⟨e, he⟩ := (inferInstance : IsPurelyInseparable.HasExponent K E).has_exponent
  let q := ringExpChar K ^ e
  have hq : 0 < q := expChar_pow_pos K (ringExpChar K) e
  have hxE : algebraMap R E x ≠ 0 := by
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective R E).ne hx
  obtain ⟨r, hr⟩ :=
    (mem_iff_pow_mem_range R K E (b : E) q hq (he b)).mp b.property
  have hrdiv : r ∈ Ideal.span {x ^ q} := by
    apply Ideal.mem_span_singleton_of_mem_map_atPrime_height_one (pow_ne_zero q hx)
    intro p hp hheight
    let A := Localization.AtPrime p
    by_cases hxp : x ∈ p
    · let : IsIntegrallyClosed A :=
        isIntegrallyClosed_of_isLocalization A p.primeCompl
          p.primeCompl_le_nonZeroDivisors
      obtain ⟨a, ha⟩ := (mem_iff_pow_mem_range A K E _ q hq (he _)).mp
        (hb p hheight hxp)
      have hinj : Function.Injective (algebraMap A E) := by
        rw [IsScalarTower.algebraMap_eq A K E]
        exact (RingHom.injective (algebraMap K E)).comp (IsFractionRing.injective A K)
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      refine ⟨a, hinj ?_⟩
      change algebraMap (Localization.AtPrime p) E
          (algebraMap R (Localization.AtPrime p) r) =
        algebraMap (Localization.AtPrime p) E
          (algebraMap R (Localization.AtPrime p) (x ^ q) * a)
      rw [map_mul]
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) E r,
        ← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) E (x ^ q),
        map_pow, hr, ha, div_pow]
      field_simp [hxE]
    · have hunit : IsUnit (algebraMap R A (x ^ q)) := by
        rw [map_pow]
        exact (IsLocalization.map_units A (⟨x, hxp⟩ : p.primeCompl)).pow q
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top.mpr hunit]
      exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hrdiv
  have hdivpow : ((b : E) / algebraMap R E x) ^ q = algebraMap R E c := by
    rw [div_pow, ← hr, hc, map_mul, map_pow]
    field_simp [hxE]
  have hint : IsIntegral R ((b : E) / algebraMap R E x) := by
    apply IsIntegral.of_pow hq
    rw [hdivpow]
    exact isIntegral_algebraMap
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨⟨_, hint⟩, Submodule.mem_top, ?_⟩
  apply Subtype.ext
  change x • ((b : E) / algebraMap R E x) = (b : E)
  rw [Algebra.smul_def]
  field_simp [hxE]

private theorem ker_heightOneToLocalImages (x : R) (hx : x ≠ 0) :
    LinearMap.ker (heightOneToLocalImages E x) =
      x • (⊤ : Submodule R S) := by
  have hxE : algebraMap R E x ≠ 0 := by
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective R E).ne hx
  apply le_antisymm
  · intro b hb
    apply mem_scalar_smul_top_of_div_integral_at_height_one R K E x hx b
    intro p hp hheight hxp
    have hpmin : p ∈ (Ideal.span {x}).minimalPrimes :=
      Ideal.mem_minimalPrimes_of_height_le
        ((Ideal.span_singleton_le_iff_mem p).mpr hxp)
        (hheight.le.trans (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_iff_ne_zero.mpr hx)))
    let i : (Ideal.span {x}).minimalPrimes := ⟨p, hpmin⟩
    change heightOneToLocalImages E x b = 0 at hb
    have hbi := congrArg (fun y ↦ (y i).val) hb
    change toAtPrimeQuotient p E
      (algebraMap R (integralClosure (Localization.AtPrime p) E) x) b = 0 at hbi
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hbi)
    have heq : (b : E) = algebraMap R E x * (t : E) := congrArg Subtype.val ht
    have hdiv : (b : E) / algebraMap R E x = (t : E) := by
      rw [heq]
      field_simp [hxE]
    rw [hdiv]
    exact t.property
  · intro b hb
    obtain ⟨c, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hb
    change heightOneToLocalImages E x (x • c) = 0
    funext p
    apply Subtype.ext
    change Ideal.Quotient.mk
      (Ideal.span {algebraMap R (integralClosure (Localization.AtPrime p.val) E) x})
      (toAtPrimeNormalization p.val E (x • c)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [map_smul, Algebra.smul_def]
    exact (Ideal.span
      {algebraMap R (integralClosure (Localization.AtPrime p.val) E) x}).mul_mem_right _
        (Ideal.subset_span (Set.mem_singleton _))

end Kernel

section Complete

variable (R K E : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field E] [Algebra R E] [FaithfulSMul R E] [Algebra K E] [IsScalarTower R K E]
  [FiniteDimensional K E] [IsPurelyInseparable K E]

local notation "S" => integralClosure R E

/-- Finiteness is requested only for the literal normalization of each actual height-one
prime quotient in the residue field of its original local normalization. -/
def HeightOneResidueNormalizationFinite : Prop :=
  ∀ (p : Ideal R) [p.IsPrime] (hp : p.height = 1),
    let _ : IsDiscreteValuationRing (Localization.AtPrime p) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one p
        (Localization.AtPrime p) hp
    AtPrimeResidueNormalizationFinite p K E

variable (hres : HeightOneResidueNormalizationFinite R K E)

include K hres

private theorem finite_heightOneLocalQuotientMap_range
    (x : R) (hx : x ≠ 0) (p : (Ideal.span {x}).minimalPrimes) :
    Module.Finite R (LinearMap.range (heightOneLocalQuotientMap E x p)) := by
  have hheight := Ideal.minimalPrime_height_one
    (mem_nonZeroDivisors_iff_ne_zero.mpr hx) p.property
  let : IsDiscreteValuationRing (Localization.AtPrime p.val) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one p.val
      (Localization.AtPrime p.val) hheight
  exact finite_range_toAtPrimeQuotient_algebraMap_of_finite_residueNormalization
    p.val K E (hres p.val hheight) x hx

private theorem isNoetherian_heightOneLocalImages
    (x : R) (hx : x ≠ 0) : IsNoetherian R (heightOneLocalImages E x) := by
  classical
  let P := (Ideal.span {x}).minimalPrimes
  let : Fintype P := (Ideal.finite_minimalPrimes_of_isNoetherianRing R
    (Ideal.span {x})).fintype
  let : ∀ p : P, Module.Finite R
      (LinearMap.range (heightOneLocalQuotientMap E x p)) :=
    fun p ↦ finite_heightOneLocalQuotientMap_range R K E hres x hx p
  let : ∀ p : P, IsNoetherian R
      (LinearMap.range (heightOneLocalQuotientMap E x p)) :=
    fun p ↦ isNoetherian_of_isNoetherianRing_of_finite R
      (LinearMap.range (heightOneLocalQuotientMap E x p))
  change IsNoetherian R
    (∀ p : P, LinearMap.range (heightOneLocalQuotientMap E x p))
  exact isNoetherian_pi (R := R) (ι := P)
    (M := fun p : P ↦ LinearMap.range (heightOneLocalQuotientMap E x p))

private theorem heightOneScalarQuotientFinite (x : R) (hx : x ≠ 0) :
    QuotientFinite (x • (⊤ : Submodule R S)) := by
  let : Module.IsTorsionFree R E := .trans_faithfulSMul R K E
  let : IsNoetherian R (heightOneLocalImages E x) :=
    isNoetherian_heightOneLocalImages R K E hres x hx
  exact quotientFinite_of_ker_eq (heightOneToLocalImages E x)
    (x • (⊤ : Submodule R S)) (ker_heightOneToLocalImages R K E x hx)

/-- The quotient of the actual normalization by any nonzero coefficient
is finite over the normal Noetherian base with finite actual height-one residue normalizations.
The product target consists only of the actual finite local images. -/
theorem finite_scalar_quotient_of_finite_heightOneResidueNormalization
    (x : R) (hx : x ≠ 0) : Module.Finite R (QuotSMulTop x S) :=
  finite_quotSMulTop_of_quotientFinite x (heightOneScalarQuotientFinite R K E hres x hx)

variable [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- The literal normalization of a complete Noetherian normal local domain
with finite actual height-one residue normalizations in any finite purely
inseparable extension of its fraction field is finite over the original base ring. -/
theorem finite_of_complete_local_normal_of_finite_heightOneResidueNormalization :
    Module.Finite R S := by
  by_cases hm : IsLocalRing.maximalIdeal R = ⊥
  · let : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm).toField
    let : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by
      rw [ringKrullDim_eq_zero_of_field R]
      exact zero_le_one)
    exact finite_of_complete_local_dimLE_one R K E
  obtain ⟨x, hxm, hx⟩ := (IsLocalRing.maximalIdeal R).ne_bot_iff.mp hm
  let : Module.Finite R (QuotSMulTop x S) :=
    finite_scalar_quotient_of_finite_heightOneResidueNormalization R K E hres x hx
  exact finite_of_isPrecomplete_of_finite_scalar_quotient R K E
    (IsLocalRing.maximalIdeal R) x hxm

end Complete

end integralClosure
