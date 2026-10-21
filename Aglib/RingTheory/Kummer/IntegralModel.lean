/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteEtale.GenericMaps
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ring

/-!
# Literal Kummer integral models from UFD exponents

For a UFD domain with a supplied normalization monoid and specified fraction field, signed
  normalized factor exponents divisible by n give an actual unit-times-nth-power decomposition.
  The polynomial quotient, scaling isomorphism, tensor generic-fiber comparison, and
  factorization statements retain level zero where the source permits it. At positive levels
  invertible in the base, the literal unit-root algebra is finite and etale. Over the stated
  normal Noetherian base, its canonical generic comparison identifies it with the literal
  integral closure in the original parameter-root algebra. UFD, normality and Noetherianity are
  retained exactly in their source sections; no regular-local factoriality, purity, or
  arithmetic realization is asserted.

Extraction source: `R5Lab.Aglib.RingTheory.Kummer.IntegralModel`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b4f8c119e6fb31b535808fd196fe83f9c35a4b4ca8e0135eb4036e46ae9b463a`.
The exact source hypotheses, actual objects and forward maps are retained under native names.
-/

@[expose] public section

noncomputable section
open Polynomial
open scoped TensorProduct
namespace Algebra.Kummer

variable {R : Type*} [CommRing R]

/-- The polynomial defining an actual nth-root algebra for any parameter and natural level. -/
abbrev rootPolynomial (n : ℕ) (u : R) : R[X] := X ^ n - C u

/-- The literal polynomial quotient adjoining a root of the supplied parameter. -/
abbrev RootAlgebra (n : ℕ) (u : R) := AdjoinRoot (rootPolynomial n u)

lemma root_pow (n : ℕ) (u : R) :
    AdjoinRoot.root (rootPolynomial n u) ^ n = algebraMap R (RootAlgebra n u) u := by
  have h := AdjoinRoot.eval₂_root (rootPolynomial n u)
  simpa [rootPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
    AdjoinRoot.algebraMap_eq] using h

lemma root_finite (n : ℕ) (hn : 0 < n) (u : R) :
    Module.Finite R (RootAlgebra n u) :=
  (monic_X_pow_sub_C u (Nat.ne_of_gt hn)).finite_adjoinRoot

lemma etale_adjoinRoot_of_isUnit_derivative (q : R[X]) (hq : q.Monic)
    (hd : IsUnit (aeval (AdjoinRoot.root q) q.derivative)) :
    Algebra.Etale R (AdjoinRoot q) := by
  let P : StandardEtalePair R := ⟨q, hq, q.derivative, 1, 0, 1, by simp⟩
  let L := Localization.Away (AdjoinRoot.mk q q.derivative)
  have hmk : IsUnit (AdjoinRoot.mk q q.derivative) := by
    simpa [AdjoinRoot.aeval_eq] using hd
  let e : P.Ring ≃ₐ[R] AdjoinRoot q := P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (AdjoinRoot q) L _ hmk).symm.restrictScalars R)
  exact Algebra.Etale.of_equiv e

lemma root_etale (n : ℕ) (hn : 0 < n) (u : Rˣ) (hnR : IsUnit (n : R)) :
    Algebra.Etale R (RootAlgebra n (u : R)) := by
  apply etale_adjoinRoot_of_isUnit_derivative _
    (monic_X_pow_sub_C (u : R) (Nat.ne_of_gt hn))
  have hr : IsUnit (AdjoinRoot.root (rootPolynomial n (u : R))) := by
    apply (isUnit_pow_iff (Nat.ne_of_gt hn)).mp
    rw [root_pow]
    exact u.isUnit.map (algebraMap R _)
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero,
    map_mul, aeval_C, aeval_X_pow]
  exact (hnR.map (algebraMap R (RootAlgebra n (u : R)))).mul (hr.pow (n - 1))

section Scale
variable {K : Type*} [Field K]

lemma scaled_root_eval (n : ℕ) (u f g : K) (hg : g ≠ 0) (hf : f = u * g ^ n) :
    (rootPolynomial n u).eval₂ (algebraMap K (RootAlgebra n f))
      (algebraMap K (RootAlgebra n f) g⁻¹ * AdjoinRoot.root (rootPolynomial n f)) = 0 := by
  simp only [rootPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, mul_pow]
  rw [root_pow, ← map_pow, ← map_mul, hf]
  simp [hg, mul_comm]

lemma scaled_root_inv_eval (n : ℕ) (u f g : K) (hf : f = u * g ^ n) :
    (rootPolynomial n f).eval₂ (algebraMap K (RootAlgebra n u))
      (algebraMap K (RootAlgebra n u) g * AdjoinRoot.root (rootPolynomial n u)) = 0 := by
  simp only [rootPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, mul_pow]
  rw [root_pow, ← map_pow, ← map_mul, hf, mul_comm]
  simp

/-- The generator-scaled isomorphism sends the root of u to g^{-1} times the root of f. -/
def scaleEquiv (n : ℕ) (u f g : K) (hg : g ≠ 0) (hf : f = u * g ^ n) :
    RootAlgebra n u ≃ₐ[K] RootAlgebra n f :=
  AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom (rootPolynomial n u) (Algebra.ofId K (RootAlgebra n f))
      (algebraMap K (RootAlgebra n f) g⁻¹ * AdjoinRoot.root (rootPolynomial n f)) (by
        simpa only [Algebra.toRingHom_ofId] using scaled_root_eval n u f g hg hf))
    (AdjoinRoot.liftAlgHom (rootPolynomial n f) (Algebra.ofId K (RootAlgebra n u))
      (algebraMap K (RootAlgebra n u) g * AdjoinRoot.root (rootPolynomial n u)) (by
        simpa only [Algebra.toRingHom_ofId] using scaled_root_inv_eval n u f g hf))
    (by
      ext
      simp only [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root, map_mul,
        AlgHom.commutes, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul]
      simp [hg])
    (by
      ext
      simp only [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root, map_mul,
        AlgHom.commutes, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul]
      simp [hg])

@[simp] lemma scaleEquiv_root (n : ℕ) (u f g : K) (hg : g ≠ 0) (hf : f = u * g ^ n) :
    scaleEquiv n u f g hg hf (AdjoinRoot.root (rootPolynomial n u)) =
      algebraMap K (RootAlgebra n f) g⁻¹ * AdjoinRoot.root (rootPolynomial n f) := by
  simp [scaleEquiv]

@[simp] lemma scaleEquiv_symm_root (n : ℕ) (u f g : K) (hg : g ≠ 0)
    (hf : f = u * g ^ n) :
    (scaleEquiv n u f g hg hf).symm (AdjoinRoot.root (rootPolynomial n f)) =
      algebraMap K (RootAlgebra n u) g * AdjoinRoot.root (rootPolynomial n u) := by
  simp [scaleEquiv]

end Scale

section Generic
variable {K : Type*} [CommRing K] [Algebra R K]

/-- Base change of the literal root algebra. -/
def genericRootEquiv (n : ℕ) (u : R) :
    K ⊗[R] RootAlgebra n u ≃ₐ[K] RootAlgebra n (algebraMap R K u) := by
  let p := rootPolynomial n u
  let q := p.map (Algebra.TensorProduct.includeRight : R →ₐ[R] K ⊗[R] R).toRingHom
  let e := Algebra.TensorProduct.rid R K K
  apply (AdjoinRoot.tensorAlgEquiv p q rfl).trans
  apply AdjoinRoot.mapAlgEquiv e q (rootPolynomial n (algebraMap R K u))
  apply Associated.of_eq
  simp [q, p, e, rootPolynomial, Algebra.smul_def]

@[simp] lemma genericRootEquiv_root (n : ℕ) (u : R) :
    genericRootEquiv (K := K) n u (1 ⊗ₜ[R] AdjoinRoot.root (rootPolynomial n u)) =
      AdjoinRoot.root (rootPolynomial n (algebraMap R K u)) := by
  simp only [genericRootEquiv, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root]
  simp only [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

end Generic

section Factorization
variable [IsDomain R] [UniqueFactorizationMonoid R] [NormalizationMonoid R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
open UniqueFactorizationMonoid

/-- Chosen normalized prime multiplicities. The choice of normalized representatives is harmless. -/
noncomputable def primeMultiplicity (a p : R) : ℕ := by
  classical
  exact (normalizedFactors a).count p

/-- Signed prime exponents in a numerator-denominator representation. -/
def signedExponent (a b p : R) : ℤ :=
  (primeMultiplicity a p : ℤ) - (primeMultiplicity b p : ℤ)

omit [IsDomain R] in
/-- The signed exponent is independent of numerator and denominator for the actual fraction
  field. -/
lemma signedExponent_eq_of_fraction_eq (a b c d : R)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : algebraMap R K a / algebraMap R K b = algebraMap R K c / algebraMap R K d)
    (p : R) : signedExponent a b p = signedExponent c d p := by
  classical
  have hbK : algebraMap R K b ≠ 0 := fun hz => hb
    ((IsFractionRing.injective R K) (by simpa only [map_zero] using hz))
  have hdK : algebraMap R K d ≠ 0 := fun hz => hd
    ((IsFractionRing.injective R K) (by simpa only [map_zero] using hz))
  have hm : a * d = c * b := (IsFractionRing.injective R K)
    (by simpa only [map_mul] using (div_eq_div_iff hbK hdK).mp h)
  have hcounts := congrArg (fun x => primeMultiplicity x p) hm
  simp only [primeMultiplicity, normalizedFactors_mul ha hd, normalizedFactors_mul hc hb,
    Multiset.count_add] at hcounts
  simp only [signedExponent, primeMultiplicity]
  omega

/-- The finite support containing all potentially nonzero signed exponents. -/
noncomputable def primeSupport (a b : R) : Finset R := by
  classical
  exact (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset

omit [IsDomain R] in
lemma primeSupport_ne_zero {a b p : R} (hp : p ∈ primeSupport a b) : p ≠ 0 := by
  classical
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)).ne_zero
  · exact (prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)).ne_zero

omit [IsDomain R] [IsFractionRing R K] in
lemma mapped_factorization (a b : R) (ha : a ≠ 0) :
    ∃ u : Rˣ, algebraMap R K a = algebraMap R K (u : R) *
      ∏ p ∈ primeSupport a b, algebraMap R K p ^ primeMultiplicity a p := by
  classical
  obtain ⟨u, hu⟩ := prod_normalizedFactors ha
  refine ⟨u, ?_⟩
  have hp : (normalizedFactors a).toFinset.prod
      (fun p => algebraMap R K p ^ primeMultiplicity a p) =
      (primeSupport a b).prod (fun p => algebraMap R K p ^ primeMultiplicity a p) := by
    apply Finset.prod_subset Finset.subset_union_left
    intro p hp hpa
    have hpa' : p ∉ normalizedFactors a := fun h => hpa (Multiset.mem_toFinset.mpr h)
    simp only [primeMultiplicity, Multiset.count_eq_zero.mpr hpa', pow_zero]
  conv_lhs => rw [← hu]
  rw [map_mul, map_multiset_prod, mul_comm, ← hp]
  congr 1
  simpa [primeMultiplicity] using
    Finset.prod_multiset_map_count (normalizedFactors a) (algebraMap R K)

omit [IsDomain R] in
/-- The actual UFD unit-times-power conclusion from signed factor multiplicities.
No locality, Noetherianity or normality is needed once factoriality is assumed. -/
theorem unit_mul_power_of_signedExponent_divisible (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (n : ℕ) (hdiv : ∀ p : R, (n : ℤ) ∣ signedExponent a b p) :
    ∃ u : Rˣ, ∃ g : K, g ≠ 0 ∧
      algebraMap R K a / algebraMap R K b = algebraMap R K (u : R) * g ^ n := by
  classical
  let s := primeSupport a b
  choose e he using hdiv
  let g : K := ∏ p ∈ s, algebraMap R K p ^ e p
  have hp0 : ∀ p ∈ s, algebraMap R K p ≠ 0 := by
    intro p hp
    exact fun hz => (primeSupport_ne_zero hp) ((IsFractionRing.injective R K) (by simpa only
      [map_zero] using hz))
  have hg : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => zpow_ne_zero _ (hp0 p hp)
  obtain ⟨ua, hua⟩ := mapped_factorization (K := K) a b ha
  obtain ⟨ub, hub⟩ := mapped_factorization (K := K) b a hb
  have hs : primeSupport b a = s := Finset.union_comm _ _
  rw [hs] at hub
  have hpow : g ^ n = (∏ p ∈ s, algebraMap R K p ^ primeMultiplicity a p) /
      (∏ p ∈ s, algebraMap R K p ^ primeMultiplicity b p) := by
    rw [← Finset.prod_div_distrib, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p hp
    rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, ← he p]
    exact zpow_natCast_sub_natCast₀ (hp0 p hp) _ _
  refine ⟨ua * ub⁻¹, g, hg, ?_⟩
  rw [hua, hub, hpow]
  simp only [Units.val_mul, map_mul, map_units_inv]
  ring

/-- A fraction-field parameter satisfies this concrete finite-support UFD divisibility encoding.
The valuation comparison is proved in the companion Valuation module; it is not an input
extension theorem. -/
def FactorizationDivisible (n : ℕ) (f : K) : Prop :=
  ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ f = algebraMap R K a / algebraMap R K b ∧
    ∀ p : R, (n : ℤ) ∣ signedExponent a b p

set_option linter.unusedSectionVars false in
-- Preserve the original explicit domain hypothesis on this source interface.
@[nolint unusedArguments]
theorem unit_mul_power (n : ℕ) (f : K) (h : FactorizationDivisible (R := R) n f) :
    ∃ u : Rˣ, ∃ g : K, g ≠ 0 ∧ f = algebraMap R K (u : R) * g ^ n := by
  obtain ⟨a, b, ha, hb, rfl, hdiv⟩ := h
  exact unit_mul_power_of_signedExponent_divisible a b ha hb n hdiv

end Factorization

section Model
variable {K : Type*} [Field K] [Algebra R K]

/-- The actual generic-fibre isomorphism from the literal finite root model to the f-Kummer
  algebra. -/
def genericModelEquiv (n : ℕ) (u : R) (f g : K) (hg : g ≠ 0)
    (hf : f = algebraMap R K u * g ^ n) :
    K ⊗[R] RootAlgebra n u ≃ₐ[K] RootAlgebra n f :=
  (genericRootEquiv n u).trans (scaleEquiv n (algebraMap R K u) f g hg hf)

@[simp] lemma genericModelEquiv_root (n : ℕ) (u : R) (f g : K) (hg : g ≠ 0)
    (hf : f = algebraMap R K u * g ^ n) :
    genericModelEquiv n u f g hg hf (1 ⊗ₜ[R] AdjoinRoot.root (rootPolynomial n u)) =
      algebraMap K (RootAlgebra n f) g⁻¹ * AdjoinRoot.root (rootPolynomial n f) := by
  simp [genericModelEquiv]

/-- Generator scaling in the forward direction: alpha = g beta under the generic isomorphism. -/
lemma generator_scaled_square (n : ℕ) (u : R) (f g : K) (hg : g ≠ 0)
    (hf : f = algebraMap R K u * g ^ n) :
    algebraMap K (RootAlgebra n f) g *
      genericModelEquiv n u f g hg hf (1 ⊗ₜ[R] AdjoinRoot.root (rootPolynomial n u)) =
      AdjoinRoot.root (rootPolynomial n f) := by
  rw [genericModelEquiv_root, ← mul_assoc, ← map_mul]
  simp [hg]

lemma genericModelEquiv_base (n : ℕ) (u : R) (f g : K) (hg : g ≠ 0)
    (hf : f = algebraMap R K u * g ^ n) (k : K) :
    genericModelEquiv n u f g hg hf (algebraMap K (K ⊗[R] RootAlgebra n u) k) =
      algebraMap K (RootAlgebra n f) k :=
  AlgEquiv.commutes _ k

lemma genericModelEquiv_symm_root (n : ℕ) (u : R) (f g : K) (hg : g ≠ 0)
    (hf : f = algebraMap R K u * g ^ n) :
    (genericModelEquiv n u f g hg hf).symm (AdjoinRoot.root (rootPolynomial n f)) =
      algebraMap K (K ⊗[R] RootAlgebra n u) g *
        (1 ⊗ₜ[R] AdjoinRoot.root (rootPolynomial n u)) := by
  apply (genericModelEquiv n u f g hg hf).injective
  rw [AlgEquiv.apply_symm_apply, map_mul, AlgEquiv.commutes]
  exact (generator_scaled_square n u f g hg hf).symm

variable [IsDomain R] [UniqueFactorizationMonoid R] [NormalizationMonoid R]
variable [IsFractionRing R K]

/-- Literal finite-etale Kummer model with the exact tensor-product generic fibre.
The divisibility hypothesis is signed UFD factor multiplicity; no global purity is claimed. -/
theorem finite_etale_model (n : ℕ) (hn : 0 < n) (hnR : IsUnit (n : R))
    (f : K) (h : FactorizationDivisible (R := R) n f) :
    ∃ (u : Rˣ) (g : K) (_hg : g ≠ 0), ∃ _hf : f = algebraMap R K (u : R) * g ^ n,
      Module.Finite R (RootAlgebra n (u : R)) ∧
      Algebra.Etale R (RootAlgebra n (u : R)) ∧
      Nonempty (K ⊗[R] RootAlgebra n (u : R) ≃ₐ[K] RootAlgebra n f) := by
  obtain ⟨u, g, hg, hf⟩ := unit_mul_power n f h
  exact ⟨u, g, hg, hf, root_finite n hn _, root_etale n hn u hnR,
    ⟨genericModelEquiv n (u : R) f g hg hf⟩⟩

end Model

section LiteralClosure
universe u
variable {S F : Type u} [CommRing S] [IsIntegrallyClosed S]
  [Field F] [Algebra S F] [IsFractionRing S F]

/-- The constructed finite-etale unit-root model is isomorphic to the LITERAL integral closure
in the original f-Kummer algebra. This uses the existing proved canonical normal-base model
comparison in Algebra.FiniteEtale.GenericMaps,
not a supplied normalization model or extension criterion. The comparison uses only the
displayed integrally closed base and fraction-field assumptions. -/
def integralClosureModelEquiv
    (n : ℕ) (hn : 0 < n) (hnS : IsUnit (n : S))
    (u : Sˣ) (f g : F) (hg : g ≠ 0) (hf : f = algebraMap S F (u : S) * g ^ n) :
    RootAlgebra n (u : S) ≃ₐ[S] integralClosure S (RootAlgebra n f) := by
  let := root_finite n hn (u : S)
  let := root_etale n hn u hnS
  exact (Algebra.FiniteEtale.GenericMaps.modelEquiv S F
    (B := RootAlgebra n (u : S))).trans
    ((genericModelEquiv n (u : S) f g hg hf).restrictScalars S).mapIntegralClosure

variable [IsDomain S] [IsNoetherianRing S]

/-- The normalization comparison retains the exact scaled generic generator. -/
lemma integralClosureModelEquiv_root (n : ℕ) (hn : 0 < n) (hnS : IsUnit (n : S))
    (u : Sˣ) (f g : F) (hg : g ≠ 0) (hf : f = algebraMap S F (u : S) * g ^ n) :
    (integralClosureModelEquiv n hn hnS u f g hg hf
        (AdjoinRoot.root (rootPolynomial n (u : S))) : RootAlgebra n f) =
      algebraMap F (RootAlgebra n f) g⁻¹ * AdjoinRoot.root (rootPolynomial n f) := by
  simp only [integralClosureModelEquiv, AlgEquiv.trans_apply, AlgEquiv.coe_mapIntegralClosure,
    Algebra.FiniteEtale.GenericMaps.modelEquiv_coe,
    AlgEquiv.coe_restrictScalars, genericModelEquiv_root]

lemma integralClosure_etale (n : ℕ) (hn : 0 < n) (hnS : IsUnit (n : S))
    (u : Sˣ) (f g : F) (hg : g ≠ 0) (hf : f = algebraMap S F (u : S) * g ^ n) :
    Algebra.Etale S (integralClosure S (RootAlgebra n f)) := by
  let := root_etale n hn u hnS
  exact Algebra.Etale.of_equiv (integralClosureModelEquiv n hn hnS u f g hg hf)

lemma integralClosure_finite (n : ℕ) (hn : 0 < n) (hnS : IsUnit (n : S))
    (u : Sˣ) (f g : F) (hg : g ≠ 0) (hf : f = algebraMap S F (u : S) * g ^ n) :
    Module.Finite S (integralClosure S (RootAlgebra n f)) := by
  let := root_finite n hn (u : S)
  exact Module.Finite.of_surjective
    (integralClosureModelEquiv n hn hnS u f g hg hf).toLinearMap
    (integralClosureModelEquiv n hn hnS u f g hg hf).surjective

variable [UniqueFactorizationMonoid S] [NormalizationMonoid S]

/-- Divisibility of signed UFD exponents implies that the literal integral closure in the
f-Kummer algebra is finite and etale over the original normal Noetherian base. The actual
height-one valuation comparison, twisted coefficient and global descent remain separate. -/
theorem finite_etale_integralClosure (n : ℕ) (hn : 0 < n) (hnS : IsUnit (n : S))
    (f : F) (h : FactorizationDivisible (R := S) n f) :
    Module.Finite S (integralClosure S (RootAlgebra n f)) ∧
      Algebra.Etale S (integralClosure S (RootAlgebra n f)) := by
  obtain ⟨u, g, hg, hf⟩ := unit_mul_power n f h
  exact ⟨integralClosure_finite n hn hnS u f g hg hf,
    integralClosure_etale n hn hnS u f g hg hf⟩

end LiteralClosure
end Algebra.Kummer
