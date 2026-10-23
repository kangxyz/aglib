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
public import Aglib.RingTheory.Localization.HeightOne
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Tactic.NormNum

/-!
# Purely inseparable normalization of a complete normal local surface

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
private def surfaceAtPrimeAlgebra (E : Type*) [Field E] [Algebra R E]
    [FaithfulSMul R E] (p : Ideal R) [p.IsPrime] :
    Algebra (Localization.AtPrime p) E :=
  (IsLocalization.lift (S := Localization.AtPrime p) (g := algebraMap R E)
    (fun s : p.primeCompl ↦ isUnit_iff_ne_zero.mpr (by
      intro h
      have hs : (s : R) = 0 := (FaithfulSMul.algebraMap_injective R E)
        (by simpa only [map_zero] using h)
      exact s.property (hs.symm ▸ p.zero_mem)))).toAlgebra

attribute [local instance] surfaceAtPrimeAlgebra

private instance surfaceAtPrimeBaseTower (E : Type*) [Field E] [Algebra R E]
    [FaithfulSMul R E] (p : Ideal R) [p.IsPrime] :
    IsScalarTower R (Localization.AtPrime p) E := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (IsLocalization.lift_comp _).symm

@[instance_reducible]
private def surfaceAtPrimeFractionAlgebra [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (p : Ideal R) [p.IsPrime] :
    Algebra (Localization.AtPrime p) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime p) K
    p.primeCompl R⁰ p.primeCompl_le_nonZeroDivisors

attribute [local instance] surfaceAtPrimeFractionAlgebra

private instance surfaceAtPrimeFractionTower [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (p : Ideal R) [p.IsPrime] :
    IsScalarTower R (Localization.AtPrime p) K :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (Localization.AtPrime p) K p.primeCompl R⁰ p.primeCompl_le_nonZeroDivisors

private instance surfaceAtPrimeIsFractionRing [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (p : Ideal R) [p.IsPrime] :
    IsFractionRing (Localization.AtPrime p) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    p.primeCompl (Localization.AtPrime p) K

private instance surfaceAtPrimeFieldTower [IsDomain R] (K E : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] [Field E]
    [Algebra R E] [FaithfulSMul R E] [Algebra K E] [IsScalarTower R K E]
    (p : Ideal R) [p.IsPrime] : IsScalarTower (Localization.AtPrime p) K E := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext p.primeCompl
  ext r
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

end LocalizationAlgebras

attribute [local instance] surfaceAtPrimeAlgebra surfaceAtPrimeFractionAlgebra

section LocalImages

variable {R : Type*} [CommRing R] (E : Type*) [Field E] [Algebra R E]
  [FaithfulSMul R E]

private instance surfaceMinimalPrimeIsPrime (x : R)
    (p : (Ideal.span {x}).minimalPrimes) : p.val.IsPrime := p.property.isPrime

private def surfaceLocalQuotientMap (x : R) (p : (Ideal.span {x}).minimalPrimes) :
    integralClosure R E →ₗ[R]
      integralClosure (Localization.AtPrime p.val) E ⧸ Ideal.span
        {algebraMap R (integralClosure (Localization.AtPrime p.val) E) x} :=
  (toAtPrimeQuotient p.val E
    (algebraMap R (integralClosure (Localization.AtPrime p.val) E) x)).toLinearMap

private def surfaceLocalImages (x : R) : Type _ :=
  ∀ p : (Ideal.span {x}).minimalPrimes,
    LinearMap.range (surfaceLocalQuotientMap E x p)

private instance surfaceLocalImagesAddCommGroup (x : R) :
    AddCommGroup (surfaceLocalImages E x) :=
  inferInstanceAs (AddCommGroup
    (∀ p : (Ideal.span {x}).minimalPrimes,
      LinearMap.range (surfaceLocalQuotientMap E x p)))

private instance surfaceLocalImagesModule (x : R) :
    Module R (surfaceLocalImages E x) :=
  inferInstanceAs (Module R
    (∀ p : (Ideal.span {x}).minimalPrimes,
      LinearMap.range (surfaceLocalQuotientMap E x p)))

private def surfaceToLocalImages (x : R) :
    integralClosure R E →ₗ[R] surfaceLocalImages E x :=
  LinearMap.pi fun p ↦ (surfaceLocalQuotientMap E x p).rangeRestrict

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

private theorem ker_surfaceToLocalImages (x : R) (hx : x ≠ 0) :
    LinearMap.ker (surfaceToLocalImages E x) =
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
    change surfaceToLocalImages E x b = 0 at hb
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
    change surfaceToLocalImages E x (x • c) = 0
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

private theorem finite_surfaceLocalQuotientMap_range [FaithfulSMul R E]
    (x : R) (hx : x ≠ 0) (p : (Ideal.span {x}).minimalPrimes) :
    Module.Finite R (LinearMap.range (surfaceLocalQuotientMap E x p)) := by
  have hheight := Ideal.minimalPrime_height_one
    (mem_nonZeroDivisors_iff_ne_zero.mpr hx) p.property
  let : IsDiscreteValuationRing (Localization.AtPrime p.val) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one p.val
      (Localization.AtPrime p.val) hheight
  let : Ring.KrullDimLE 1 (R ⧸ p.val) := primeQuotient_dimLE_one R p.val x hx
    (p.property.le (Ideal.subset_span (Set.mem_singleton x)))
  exact finite_range_toAtPrimeQuotient_algebraMap p.val K E x hx

private theorem isNoetherian_surfaceLocalImages [FaithfulSMul R E]
    (x : R) (hx : x ≠ 0) : IsNoetherian R (surfaceLocalImages E x) := by
  classical
  let P := (Ideal.span {x}).minimalPrimes
  let : Fintype P := (Ideal.finite_minimalPrimes_of_isNoetherianRing R
    (Ideal.span {x})).fintype
  let : ∀ p : P, Module.Finite R
      (LinearMap.range (surfaceLocalQuotientMap E x p)) :=
    fun p ↦ finite_surfaceLocalQuotientMap_range R K E x hx p
  let : ∀ p : P, IsNoetherian R
      (LinearMap.range (surfaceLocalQuotientMap E x p)) :=
    fun p ↦ isNoetherian_of_isNoetherianRing_of_finite R
      (LinearMap.range (surfaceLocalQuotientMap E x p))
  change IsNoetherian R
    (∀ p : P, LinearMap.range (surfaceLocalQuotientMap E x p))
  exact isNoetherian_pi (R := R) (ι := P)
    (M := fun p : P ↦ LinearMap.range (surfaceLocalQuotientMap E x p))

private theorem surfaceScalarQuotientFinite (x : R) (hx : x ≠ 0) :
    QuotientFinite (x • (⊤ : Submodule R S)) := by
  let : Module.IsTorsionFree R E := .trans_faithfulSMul R K E
  let : IsNoetherian R (surfaceLocalImages E x) :=
    isNoetherian_surfaceLocalImages R K E x hx
  exact quotientFinite_of_ker_eq (surfaceToLocalImages E x)
    (x • (⊤ : Submodule R S)) (ker_surfaceToLocalImages R K E x hx)

/-- The quotient of the actual normalization by any nonzero coefficient
is finite over a complete normal local base of dimension at most two.
The product target consists only of the actual finite local images. -/
theorem finite_scalar_quotient_of_complete_local_normal_dimLE_two
    (x : R) (hx : x ≠ 0) : Module.Finite R (QuotSMulTop x S) :=
  finite_quotSMulTop_of_quotientFinite x (surfaceScalarQuotientFinite R K E x hx)

/-- The literal normalization of a complete Noetherian normal local domain
of dimension at most two in any finite purely inseparable extension of its
fraction field is finite over the original base ring. -/
theorem finite_of_complete_local_normal_dimLE_two_of_isPurelyInseparable :
    Module.Finite R S := by
  by_cases hm : IsLocalRing.maximalIdeal R = ⊥
  · let : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm).toField
    let : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by
      rw [ringKrullDim_eq_zero_of_field R]
      exact zero_le_one)
    exact finite_of_complete_local_dimLE_one R K E
  obtain ⟨x, hxm, hx⟩ := (IsLocalRing.maximalIdeal R).ne_bot_iff.mp hm
  let : Module.Finite R (QuotSMulTop x S) :=
    finite_scalar_quotient_of_complete_local_normal_dimLE_two R K E x hx
  exact finite_of_isPrecomplete_of_finite_scalar_quotient R K E
    (IsLocalRing.maximalIdeal R) x hxm

end Complete

end integralClosure
