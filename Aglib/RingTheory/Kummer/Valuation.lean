/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.IntegralModel
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.AsSubring

/-!
# Height-one normalized valuations and Kummer exponents

For a Noetherian UFD domain with a normalization monoid and its specified fraction field, the
  literal height-one prime localization is a DVR. Its valuation is normalized by uniformizer
  value exp(-1), and its integer order is positive one on a uniformizer. The signed order of a
  nonzero fraction is proved equal to the normalized factor exponent. Divisibility at every
  actual height-one prime is equivalent to FactorizationDivisible for the same nonzero
  parameter, including level zero. The final finite-etale integral-closure consequence retains
  positive n, invertibility and the original normal Noetherian UFD assumptions. No
  residue/cohomology dictionary or purity theorem is used.

Extraction source: `R5Lab.Aglib.RingTheory.Kummer.Valuation`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d6914b205d525a4df4e5146feeb1ce30a485140820150252dd9bf84bc62b634c`.
The exact source hypotheses, actual objects and forward maps are retained under native names.
-/

@[expose] public section

namespace Algebra.Kummer

open UniqueFactorizationMonoid
open scoped WithZero

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [NormalizationMonoid R] [IsNoetherianRing R]

omit [NormalizationMonoid R] in
/-- In a Noetherian UFD the literal localization at a height-one prime is a DVR. -/
theorem atPrime_isDiscreteValuationRing (P : Ideal R) [P.IsPrime] (hP : P.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let A := Localization.AtPrime P
  have hP0 : P ≠ ⊥ := P.ne_bot_of_height_eq_one hP
  obtain ⟨p, hp⟩ := isPrincipal_of_height_eq_one hP
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap R A p} := by
    calc
      IsLocalRing.maximalIdeal A = Ideal.map (algebraMap R A) P :=
        (IsLocalization.AtPrime.map_eq_maximalIdeal P A).symm
      _ = Ideal.map (algebraMap R A) (Ideal.span {p}) := congrArg (Ideal.map (algebraMap R A)) hp
      _ = Ideal.span {algebraMap R A p} := by rw [Ideal.map_span, Set.image_singleton]
  have hmaxPrincipal : (IsLocalRing.maximalIdeal A).IsPrincipal := by
    rw [hmax]
    infer_instance
  have hn : ¬ IsField A := by
    intro hfield
    have hz : IsLocalRing.maximalIdeal A = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    obtain ⟨x, hx, hx0⟩ := P.ne_bot_iff.mp hP0
    have hxm : algebraMap R A x ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff A P x).mpr hx
    rw [hz, Ideal.mem_bot] at hxm
    exact hx0 (FaithfulSMul.algebraMap_injective R A (by simpa using hxm))
  exact ((IsDiscreteValuationRing.TFAE A hn).out 5 1).mp hmaxPrincipal

omit [UniqueFactorizationMonoid R] [NormalizationMonoid R] in
/-- A prime element generates a literal height-one prime ideal. -/
theorem height_span_prime {p : R} (hp : Prime p) : (Ideal.span {p}).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hp.ne_zero) hp.not_isUnit

omit [UniqueFactorizationMonoid R] [NormalizationMonoid R] [IsNoetherianRing R] in
/-- The prime element is a uniformizer in the localization at its own prime ideal. -/
theorem irreducible_atPrime_span {p : R} (hp : Prime p) :
    let : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    Irreducible (algebraMap R (Localization.AtPrime (Ideal.span {p})) p) := by
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  let A := Localization.AtPrime (Ideal.span {p})
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
  · exact fun h => hp.ne_zero (FaithfulSMul.algebraMap_injective R A (by simpa using h))
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {p}) A,
      Ideal.map_span, Set.image_singleton]

/-- Localizing at `(p)` preserves its multiplicity, as the normalized DVR additive valuation. -/
theorem addVal_atPrime_span_algebraMap {p a : R} (hp : Prime p) (ha : a ≠ 0) :
    let : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    let := atPrime_isDiscreteValuationRing (Ideal.span {p}) (height_span_prime hp)
    IsDiscreteValuationRing.addVal (Localization.AtPrime (Ideal.span {p}))
      (algebraMap R (Localization.AtPrime (Ideal.span {p})) a) = multiplicity p a := by
  classical
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have := atPrime_isDiscreteValuationRing (Ideal.span {p}) (height_span_prime hp)
  let A := Localization.AtPrime (Ideal.span {p})
  have hfin : FiniteMultiplicity p a := finiteMultiplicity_of_emultiplicity_eq_natCast
    (emultiplicity_eq_count_normalizedFactors hp.irreducible ha)
  obtain ⟨c, hac, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hc : IsUnit (algebraMap R A c) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff A (Ideal.span {p}) c).mpr
      (by simpa only [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton] using hpc)
  obtain ⟨u, hu⟩ := hc
  apply IsDiscreteValuationRing.addVal_def _ u (irreducible_atPrime_span hp)
  calc
    algebraMap R A a = (algebraMap R A p) ^ multiplicity p a * algebraMap R A c :=
      by simpa only [map_mul, map_pow] using congrArg (algebraMap R A) hac
    _ = (u : A) * (algebraMap R A p) ^ multiplicity p a := by rw [← hu, mul_comm]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The canonical localization-to-fraction-field map supplies the local algebra structure. -/
@[instance_reducible]
noncomputable def atPrimeFractionAlgebra (P : Ideal R) [P.IsPrime] :
    Algebra (Localization.AtPrime P) K :=
  (Localization.mapToFractionRing K P.primeCompl (Localization.AtPrime P)
    P.primeCompl_le_nonZeroDivisors).toRingHom.toAlgebra

omit [UniqueFactorizationMonoid R] [NormalizationMonoid R] [IsNoetherianRing R] in
/-- Compatibility of the canonical localization-to-fraction-field map with the map from R. -/
theorem atPrimeFraction_isScalarTower (P : Ideal R) [P.IsPrime] :
    let := atPrimeFractionAlgebra (K := K) P
    IsScalarTower R (Localization.AtPrime P) K := by
  let := atPrimeFractionAlgebra (K := K) P
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (Localization.mapToFractionRing K P.primeCompl (Localization.AtPrime P)
    P.primeCompl_le_nonZeroDivisors).commutes x |>.symm

omit [UniqueFactorizationMonoid R] [NormalizationMonoid R] [IsNoetherianRing R] in
/-- The given actual fraction field is also the fraction field of the actual local ring. -/
theorem atPrimeFraction_isFractionRing (P : Ideal R) [P.IsPrime] :
    let := atPrimeFractionAlgebra (K := K) P
    IsFractionRing (Localization.AtPrime P) K := by
  let := atPrimeFractionAlgebra (K := K) P
  have := atPrimeFraction_isScalarTower (K := K) P
  exact IsFractionRing.isFractionRing_of_isLocalization P.primeCompl
    (Localization.AtPrime P) K P.primeCompl_le_nonZeroDivisors

/-- The normalized adic valuation supplied by the literal height-one local DVR, on the
same fraction field K. A local uniformizer has value exp(-1). -/
noncomputable def heightOneValuation (P : Ideal R) [P.IsPrime] (hP : P.height = 1) :
    Valuation K ℤᵐ⁰ := by
  have := atPrime_isDiscreteValuationRing P hP
  let := atPrimeFractionAlgebra (K := K) P
  have := atPrimeFraction_isScalarTower (K := K) P
  have := atPrimeFraction_isFractionRing (K := K) P
  exact (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime P)).valuation K

omit [NormalizationMonoid R] in
/-- The valuation ring is precisely the image of the literal prime localization under its
canonical map to the same fraction field. -/
theorem heightOneValuationSubring_eq (P : Ideal R) [P.IsPrime] (hP : P.height = 1) :
    (heightOneValuation (K := K) P hP).valuationSubring.toSubring =
      Subring.map (Localization.mapToFractionRing K P.primeCompl (Localization.AtPrime P)
        P.primeCompl_le_nonZeroDivisors).toRingHom ⊤ := by
  have := atPrime_isDiscreteValuationRing P hP
  let := atPrimeFractionAlgebra (K := K) P
  have := atPrimeFraction_isScalarTower (K := K) P
  have := atPrimeFraction_isFractionRing (K := K) P
  exact (IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
    (A := Localization.AtPrime P) (K := K)).symm

omit [NormalizationMonoid R] in
/-- Every local uniformizer has the normalization value exp(-1), on the actual field. -/
theorem heightOneValuation_uniformizer (P : Ideal R) [P.IsPrime] (hP : P.height = 1)
    (π : Localization.AtPrime P) (hπ : Irreducible π) :
    heightOneValuation (K := K) P hP
      (Localization.mapToFractionRing K P.primeCompl (Localization.AtPrime P)
        P.primeCompl_le_nonZeroDivisors π) = WithZero.exp (-1 : ℤ) := by
  have := atPrime_isDiscreteValuationRing P hP
  let := atPrimeFractionAlgebra (K := K) P
  have := atPrimeFraction_isScalarTower (K := K) P
  have := atPrimeFraction_isFractionRing (K := K) P
  change (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime P)).valuation K
    (algebraMap (Localization.AtPrime P) K π) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,
    IsDiscreteValuationRing.addVal_uniformizer hπ]
  rfl

/-- The integer order convention is positive on a local uniformizer. The value at zero is
junk; applications below impose nonzeroness. -/
noncomputable def heightOneOrder (P : Ideal R) [P.IsPrime] (hP : P.height = 1) (f : K) : ℤ :=
  -WithZero.log (heightOneValuation (K := K) P hP f)

omit [NormalizationMonoid R] in
/-- Every local uniformizer has integer order one under the positive-order convention. -/
theorem heightOneOrder_uniformizer (P : Ideal R) [P.IsPrime] (hP : P.height = 1)
    (π : Localization.AtPrime P) (hπ : Irreducible π) :
    heightOneOrder (K := K) P hP
      (Localization.mapToFractionRing K P.primeCompl (Localization.AtPrime P)
        P.primeCompl_le_nonZeroDivisors π) = 1 := by
  unfold heightOneOrder
  rw [heightOneValuation_uniformizer P hP π hπ]
  simp

/-- Exact local valuation/multiplicity correspondence for every prime element and nonzero a. -/
theorem heightOneValuation_span_algebraMap {p a : R} (hp : Prime p) (ha : a ≠ 0) :
    let : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    heightOneValuation (K := K) (Ideal.span {p}) (height_span_prime hp)
      (algebraMap R K a) = WithZero.exp (-(multiplicity p a : ℤ)) := by
  classical
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  let P := Ideal.span {p}
  let A := Localization.AtPrime P
  have := atPrime_isDiscreteValuationRing P (height_span_prime hp)
  let := atPrimeFractionAlgebra (K := K) P
  have := atPrimeFraction_isScalarTower (K := K) P
  have := atPrimeFraction_isFractionRing (K := K) P
  change (IsDiscreteValuationRing.maximalIdeal A).valuation K (algebraMap R K a) = _
  rw [IsScalarTower.algebraMap_apply R A K a,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,
    addVal_atPrime_span_algebraMap hp ha]
  rfl

/-- Exact normalized local valuation of a numerator/denominator fraction. -/
theorem heightOneValuation_span_div {p a b : R} (hp : Prime p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    let : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    heightOneValuation (K := K) (Ideal.span {p}) (height_span_prime hp)
      (algebraMap R K a / algebraMap R K b) =
      WithZero.exp (-((multiplicity p a : ℤ) - (multiplicity p b : ℤ))) := by
  dsimp only
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  rw [map_div₀, heightOneValuation_span_algebraMap hp ha,
    heightOneValuation_span_algebraMap hp hb, ← WithZero.exp_sub]
  congr 1
  ring

/-- The integer order at `(p)` is the signed multiplicity of a/b. -/
theorem heightOneOrder_span_div_multiplicity {p a b : R} (hp : Prime p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    let : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    heightOneOrder (K := K) (Ideal.span {p}) (height_span_prime hp)
      (algebraMap R K a / algebraMap R K b) =
      (multiplicity p a : ℤ) - (multiplicity p b : ℤ) := by
  dsimp only
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  unfold heightOneOrder
  rw [heightOneValuation_span_div hp ha hb]
  simp

/-- For a normalized prime, the literal height-one local order equals Kummer's existing
signedExponent. The theorem does not take factor divisibility as an assumption. -/
theorem heightOneOrder_span_div {p a b : R} (hp : Prime p) (hnorm : normalize p = p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    let : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    heightOneOrder (K := K) (Ideal.span {p}) (height_span_prime hp)
      (algebraMap R K a / algebraMap R K b) = signedExponent a b p := by
  dsimp only
  classical
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  rw [heightOneOrder_span_div_multiplicity hp ha hb]
  simp only [signedExponent, primeMultiplicity,
    multiplicity_eq_count_normalizedFactors hp.irreducible ha,
    multiplicity_eq_count_normalizedFactors hp.irreducible hb, hnorm]

omit [IsNoetherianRing R] in
/-- Every literal height-one prime has a normalized prime generator in a UFD. -/
theorem heightOne_exists_normalized_prime_generator (P : Ideal R) [P.IsPrime]
    (hP : P.height = 1) : ∃ p : R, Prime p ∧ normalize p = p ∧ P = Ideal.span {p} := by
  obtain ⟨q, hqmem, hq⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot
    (inferInstance : P.IsPrime) (P.ne_bot_of_height_eq_one hP)
  refine ⟨normalize q, (normalize_associated q).prime_iff.mpr hq, normalize_idem q, ?_⟩
  calc
    P = Ideal.span {q} := P.eq_span_singleton_of_height_eq_one hP hqmem hq
    _ = Ideal.span {normalize q} :=
      Ideal.span_singleton_eq_span_singleton.mpr (associated_normalize q)

/-- For any literal height-one prime and a normalized prime generator, the actual integer
order agrees with the existing signed UFD exponent of a/b. -/
theorem heightOneOrder_div_of_generator (P : Ideal R) [P.IsPrime] (hP : P.height = 1)
    {p a b : R} (hp : Prime p) (hnorm : normalize p = p) (hspan : P = Ideal.span {p})
    (ha : a ≠ 0) (hb : b ≠ 0) :
    heightOneOrder (K := K) P hP (algebraMap R K a / algebraMap R K b) =
      signedExponent a b p := by
  subst P
  exact heightOneOrder_span_div hp hnorm ha hb

/-- Divisibility of the actual normalized valuations at every literal height-one prime implies
Kummer's finite-support factorization hypothesis for the same nonzero field parameter. -/
theorem factorizationDivisible_of_heightOneOrder (n : ℕ) (f : K) (hf : f ≠ 0)
    (hdiv : ∀ (P : Ideal R) [P.IsPrime] (hP : P.height = 1),
      (n : ℤ) ∣ heightOneOrder (K := K) P hP f) :
    FactorizationDivisible (R := R) n f := by
  classical
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply hf
    rw [← hab, ha, map_zero, zero_div]
  refine ⟨a, b, ha0, hb0, hab.symm, ?_⟩
  intro p
  by_cases hmem : p ∈ normalizedFactors a ∨ p ∈ normalizedFactors b
  · have hp : Prime p := hmem.elim (prime_of_normalized_factor p) (prime_of_normalized_factor p)
    have hnorm : normalize p = p :=
      hmem.elim (normalize_normalized_factor p) (normalize_normalized_factor p)
    have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    have hv := hdiv (Ideal.span {p}) (height_span_prime hp)
    rwa [← hab, heightOneOrder_span_div hp hnorm ha0 hb0] at hv
  · have hpa : p ∉ normalizedFactors a := fun h => hmem (Or.inl h)
    have hpb : p ∉ normalizedFactors b := fun h => hmem (Or.inr h)
    simp only [signedExponent, primeMultiplicity, Multiset.count_eq_zero.mpr hpa,
      Multiset.count_eq_zero.mpr hpb, Nat.cast_zero, sub_zero]
    exact dvd_zero _

/-- The converse correspondence at every literal height-one prime, for the same Kummer
parameter. This does not assert any residue/cohomology dictionary. -/
theorem heightOneOrder_divisible_of_factorizationDivisible (n : ℕ) (f : K)
    (hf : FactorizationDivisible (R := R) n f) (P : Ideal R) [P.IsPrime] (hP : P.height = 1) :
    (n : ℤ) ∣ heightOneOrder (K := K) P hP f := by
  obtain ⟨a, b, ha, hb, rfl, hdiv⟩ := hf
  obtain ⟨p, hp, hnorm, hspan⟩ := heightOne_exists_normalized_prime_generator P hP
  rw [heightOneOrder_div_of_generator P hP hp hnorm hspan ha hb]
  exact hdiv p

/-- Exact equivalence between the existing Kummer factor hypothesis and divisibility of the
normalized orders at all actual height-one local DVRs; zero is excluded on both sides. -/
theorem factorizationDivisible_iff_heightOneOrder (n : ℕ) (f : K) :
    FactorizationDivisible (R := R) n f ↔ f ≠ 0 ∧
      ∀ (P : Ideal R) [P.IsPrime] (hP : P.height = 1),
        (n : ℤ) ∣ heightOneOrder (K := K) P hP f := by
  constructor
  · intro hf
    refine ⟨?_, heightOneOrder_divisible_of_factorizationDivisible n f hf⟩
    obtain ⟨a, b, ha, hb, rfl, hdiv⟩ := hf
    exact div_ne_zero
      (fun h => ha ((IsFractionRing.injective R K) (by simpa only [map_zero] using h)))
      (fun h => hb ((IsFractionRing.injective R K) (by simpa only [map_zero] using h)))
  · rintro ⟨hf, hdiv⟩
    exact factorizationDivisible_of_heightOneOrder n f hf hdiv

section LiteralClosure
universe u
variable {S F : Type u} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
  [IsNoetherianRing S] [UniqueFactorizationMonoid S] [NormalizationMonoid S]
  [Field F] [Algebra S F] [IsFractionRing S F]

/-- Height-one order divisibility gives finiteness and étaleness of the literal integral closure
in the full original Kummer algebra. Positivity and invertibility are retained from Kummer;
no primitiveness, connectedness or restriction on n = 1 is imposed. -/
theorem finite_etale_integralClosure_of_heightOneOrder
    (n : ℕ) (hn : 0 < n) (hnS : IsUnit (n : S)) (f : F) (hf : f ≠ 0)
    (hdiv : ∀ (P : Ideal S) [P.IsPrime] (hP : P.height = 1),
      (n : ℤ) ∣ heightOneOrder (K := F) P hP f) :
    Module.Finite S (integralClosure S (RootAlgebra n f)) ∧
      Algebra.Etale S (integralClosure S (RootAlgebra n f)) := by
  exact finite_etale_integralClosure n hn hnS f
    (factorizationDivisible_of_heightOneOrder n f hf hdiv)

end LiteralClosure
end Algebra.Kummer
