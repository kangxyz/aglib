/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Topology.Sober
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.RingTheory.Localization.Pi
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.Topology.DenseEmbedding

/-!
# The literal two-component pinched curve: Affine

Source: frozen R5 `Curves/Cyclic/TwoGon/Affine.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The actual ring maps, gluing arrows and component indices are retained.
This leaf does not construct a marked model or assume a model-existence theorem.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

namespace AlgebraicGeometry.Scheme.TwoGon.Affine

variable (k : Type u) [Field k]

/-- The product polynomial ring of the two normalization components. -/
abbrev NormalizationRing := k[X] × k[X]

/-- Evaluation at `a` on the left polynomial component. -/
def leftEvaluation (a : k) : NormalizationRing k →ₐ[k] k :=
  (aeval a).comp (AlgHom.fst k k[X] k[X])
/-- Evaluation at `a` on the right polynomial component. -/
def rightEvaluation (a : k) : NormalizationRing k →ₐ[k] k :=
  (aeval a).comp (AlgHom.snd k k[X] k[X])

/-- The two actual components are identified precisely at the prescribed values. -/
def nodeRing : Subalgebra k (NormalizationRing k) :=
  (leftEvaluation k 0).equalizer (rightEvaluation k 0) ⊓
    (leftEvaluation k 1).equalizer (rightEvaluation k 1)

@[simp] theorem mem_nodeRing (p : NormalizationRing k) :
    p ∈ nodeRing k ↔ p.1.eval 0 = p.2.eval 0 ∧ p.1.eval 1 = p.2.eval 1 := Iff.rfl

/-- Every diagonal polynomial belongs to the pinched ring. -/
def diagonal (p : k[X]) : nodeRing k := ⟨(p, p), by simp⟩

/-- The two component idempotents generate the normalization module. -/
def generators : (nodeRing k × nodeRing k) →ₗ[nodeRing k] NormalizationRing k :=
  (LinearMap.toSpanSingleton (nodeRing k) (NormalizationRing k) (1, 0)).coprod
    (LinearMap.toSpanSingleton (nodeRing k) (NormalizationRing k) (0, 1))

theorem generators_surjective : Function.Surjective (generators k) := by
  rintro ⟨p, q⟩
  refine ⟨(diagonal k p, diagonal k q), ?_⟩
  change (p, p) * (1, 0) + (q, q) * (0, 1) = (p, q)
  ext <;> simp

/-- The product polynomial normalization is finite over the two-gon pinching algebra. -/
instance normalization_finite : Module.Finite (nodeRing k) (NormalizationRing k) :=
  Module.Finite.of_surjective (generators k) (generators_surjective k)

/-- The product polynomial normalization is integral over the two-gon pinching algebra. -/
instance normalization_integral : Algebra.IsIntegral (nodeRing k) (NormalizationRing k) :=
  Algebra.IsIntegral.of_finite _ _

/-- The spectrum of the product polynomial normalization ring. -/
abbrev normalizationScheme : Scheme.{u} := Spec (.of (NormalizationRing k))
/-- The spectrum of the two-gon pinching algebra. -/
abbrev nodeScheme : Scheme.{u} := Spec (.of (nodeRing k))
/-- The affine normalization morphism induced by inclusion of the two-gon pinching algebra. -/
def normalizationMap : normalizationScheme k ⟶ nodeScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap (nodeRing k) (NormalizationRing k)))

theorem normalizationMap_finite : IsFinite (normalizationMap k) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

theorem normalizationMap_surjective : Function.Surjective (normalizationMap k) :=
  RingHom.IsIntegral.comap_surjective
    ((algebraMap_isIntegral_iff).mpr (inferInstance :
      Algebra.IsIntegral (nodeRing k) (NormalizationRing k))) Subtype.val_injective

/-- Evaluation at a in the left normalization component, as an actual prime. -/
def leftBranch (a : k) : normalizationScheme k :=
  ⟨RingHom.ker (leftEvaluation k a).toRingHom,
    (RingHom.ker_isMaximal_of_surjective _ (fun x => ⟨(C x, 0), by simp [leftEvaluation]⟩)).isPrime⟩
/-- Evaluation at a in the right normalization component, as an actual prime. -/
def rightBranch (a : k) : normalizationScheme k :=
  ⟨RingHom.ker (rightEvaluation k a).toRingHom,
    (RingHom.ker_isMaximal_of_surjective _ (fun x => ⟨(0, C x), by simp
      [rightEvaluation]⟩)).isPrime⟩

/-- The image of the left evaluation prime at `a` under the affine normalization map. -/
def nodePoint (a : k) : nodeScheme k := normalizationMap k (leftBranch k a)

theorem branches_distinct (a b : k) : leftBranch k a ≠ rightBranch k b := by
  intro h
  have he : ((0, 1) : NormalizationRing k) ∈ (leftBranch k a).asIdeal := by
    simp [leftBranch, leftEvaluation]
  rw [h] at he
  simp [rightBranch, rightEvaluation] at he

theorem branches_same_image (a : k) (ha : a = 0 ∨ a = 1) :
    normalizationMap k (leftBranch k a) = normalizationMap k (rightBranch k a) := by
  apply PrimeSpectrum.ext
  ext p
  change (p : NormalizationRing k).1.eval a = 0 ↔ (p : NormalizationRing k).2.eval a = 0
  have hp := (mem_nodeRing k p).mp p.property
  rcases ha with rfl | rfl
  · rw [hp.1]
  · rw [hp.2]

/-- The two target nodes are distinct, detected by the diagonal affine parameter. -/
theorem nodePoints_distinct : nodePoint k 0 ≠ nodePoint k 1 := by
  intro h
  have hx : diagonal k X ∈ (nodePoint k 0).asIdeal := by
    change eval 0 (X : k[X]) = 0
    simp
  rw [h] at hx
  change eval 1 (X : k[X]) = 0 at hx
  simp at hx

/-- The source is the actual disjoint union on prime spectra, not labels. -/
theorem normalizationPoint_cases (p : normalizationScheme k) :
    (∃ q : PrimeSpectrum k[X], p = PrimeSpectrum.comap (RingHom.fst k[X] k[X]) q) ∨
    (∃ q : PrimeSpectrum k[X], p = PrimeSpectrum.comap (RingHom.snd k[X] k[X]) q) := by
  let e := PrimeSpectrum.primeSpectrumProd k[X] k[X]
  have he := e.symm_apply_apply p
  cases h : e p with
  | inl q =>
      left
      refine ⟨q, ?_⟩
      rw [h, PrimeSpectrum.primeSpectrumProd_symm_inl] at he
      exact he.symm
  | inr q =>
      right
      refine ⟨q, ?_⟩
      rw [h, PrimeSpectrum.primeSpectrumProd_symm_inr] at he
      exact he.symm

/-- The evaluation prime in a single affine normalization component. -/
def linePoint (a : k) : PrimeSpectrum k[X] :=
  ⟨RingHom.ker (evalRingHom a), (RingHom.ker_isMaximal_of_surjective (evalRingHom a)
    (fun x => ⟨C x, by simp⟩)).isPrime⟩

theorem linePoint_eq_of_mem (p : PrimeSpectrum k[X]) (a : k)
    (h : X - C a ∈ p.asIdeal) : p = linePoint k a := by
  apply PrimeSpectrum.ext
  symm
  apply (RingHom.ker_isMaximal_of_surjective (evalRingHom a)
    (fun x => ⟨C x, by simp⟩)).eq_of_le p.isPrime.ne_top
  rw [ker_evalRingHom]
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)

/-- A contracted node point forces the component prime to be evaluation at a. -/
theorem affine_normalization_fibre (a : k) (ha : a = 0 ∨ a = 1)
    (p : normalizationScheme k) :
    normalizationMap k p = nodePoint k a ↔ p = leftBranch k a ∨ p = rightBranch k a := by
  constructor
  · intro h
    have hx : diagonal k (X - C a) ∈ (normalizationMap k p).asIdeal := by
      rw [h]
      change eval a (X - C a : k[X]) = 0
      simp
    rcases normalizationPoint_cases k p with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · have hq : q = linePoint k a :=
        linePoint_eq_of_mem k q a hx
      left
      rw [hq]
      rfl
    · have hq : q = linePoint k a :=
        linePoint_eq_of_mem k q a hx
      right
      rw [hq]
      rfl
  · rintro (rfl | rfl)
    · rfl
    · exact (branches_same_image k a ha).symm

/-- Each actual node fibre has exactly two primes, one in each component. -/
theorem affine_normalization_fibre_card (a : k) (ha : a = 0 ∨ a = 1) :
    Nat.card {p : normalizationScheme k // normalizationMap k p = nodePoint k a} = 2 := by
  change ({p : normalizationScheme k | normalizationMap k p = nodePoint k a} : Set _).ncard = 2
  have he : {p : normalizationScheme k | normalizationMap k p = nodePoint k a} =
      {leftBranch k a, rightBranch k a} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      affine_normalization_fibre k a ha]
  rw [he, Set.ncard_pair (branches_distinct k a a)]

/-- Multiplication by the diagonal conductor sends every normalization element to A. -/
def conductor : nodeRing k := diagonal k (X * (X - 1))
/-- Multiplication by `X * (X - 1)` on both components, with values in the pinching algebra. -/
def conductorMul (p : NormalizationRing k) : nodeRing k :=
  ⟨((X * (X - 1)) * p.1, (X * (X - 1)) * p.2), by simp⟩

/-- The two-gon pinching algebra localized away from the conductor element. -/
abbrev nodeOverlapRing := Localization.Away (conductor k)
/-- The product polynomial normalization localized away from the conductor element. -/
abbrev normalizationOverlapRing := Localization.Away (conductor k : NormalizationRing k)
/-- The map on conductor localizations induced by the normalization inclusion. -/
def localizationComparison : nodeOverlapRing k →+* normalizationOverlapRing k :=
  Localization.awayMap (nodeRing k).val.toRingHom (conductor k)

/-- The actual inclusion is an isomorphism after inverting its conductor. -/
theorem localizationComparison_bijective : Function.Bijective (localizationComparison k) := by
  change Function.Bijective (Localization.awayMap (nodeRing k).val.toRingHom (conductor k))
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro a ha
    have hz : a = 0 := Subtype.ext ha
    exact ⟨0, by simp [hz]⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro p
    exact ⟨conductorMul k p, 1, by
      simp only [pow_one]
      apply Prod.ext <;> rfl⟩

/-- The conductor localization of the pinching algebra identified with that of the normalization. -/
def conductorLocalizationEquiv : nodeOverlapRing k ≃+* normalizationOverlapRing k :=
  RingEquiv.ofBijective (localizationComparison k) (localizationComparison_bijective k)

/-- The two independent evaluation differences are the actual normalization defect. -/
def branchDifference : NormalizationRing k →ₗ[k] k × k :=
  ((leftEvaluation k 0).toLinearMap - (rightEvaluation k 0).toLinearMap).prod
    ((leftEvaluation k 1).toLinearMap - (rightEvaluation k 1).toLinearMap)

theorem branchDifference_surjective : Function.Surjective (branchDifference k) := by
  rintro ⟨a, b⟩
  refine ⟨(C a + C (b - a) * X, 0), ?_⟩
  ext <;> simp [branchDifference, leftEvaluation, rightEvaluation]

theorem branchDifference_ker : (branchDifference k).ker = (nodeRing k).toSubmodule := by
  ext p
  simp [branchDifference, leftEvaluation, rightEvaluation, sub_eq_zero,
    mem_nodeRing]

/-- The normalization quotient identified with the pair of endpoint evaluation differences. -/
def normalizationDefectEquiv :
    (NormalizationRing k ⧸ (nodeRing k).toSubmodule) ≃ₗ[k] (k × k) := by
  rw [← branchDifference_ker]
  exact (branchDifference k).quotKerEquivOfSurjective (branchDifference_surjective k)

theorem normalizationDefect_finrank :
    Module.finrank k (NormalizationRing k ⧸ (nodeRing k).toSubmodule) = 2 := by
  rw [(normalizationDefectEquiv k).finrank_eq]
  simp

/-- The two-gon pinching algebra is finitely generated over `k`. -/
instance nodeRing_finiteType : Algebra.FiniteType k (nodeRing k) :=
  ⟨fg_of_fg_of_fg k (nodeRing k) (NormalizationRing k)
    Algebra.FiniteType.out Module.Finite.fg_top Subtype.val_injective⟩

/-- The ambient ring is the product of the two actual component function fields. -/
abbrev RationalFunctions := FractionRing k[X] × FractionRing k[X]

/-- The product polynomial ring included in the product of its two rational function fields. -/
def fractionMap : NormalizationRing k →+* RationalFunctions k :=
  (algebraMap k[X] (FractionRing k[X])).prodMap (algebraMap k[X] (FractionRing k[X]))

/-- The product rational function fields as an algebra over the polynomial normalization ring. -/
instance normalizationFractionAlgebra : Algebra (NormalizationRing k) (RationalFunctions k) :=
  (fractionMap k).toAlgebra
/-- The product rational function fields as an algebra over the two-gon pinching algebra. -/
instance nodeFractionAlgebra : Algebra (nodeRing k) (RationalFunctions k) :=
  ((fractionMap k).comp (nodeRing k).val.toRingHom).toAlgebra
/-- The rational-function scalar actions are compatible with the normalization inclusion. -/
instance nodeFractionTower : IsScalarTower (nodeRing k) (NormalizationRing k)
  (RationalFunctions k) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Integral closure in the product of the component function fields, proved
componentwise from actual polynomials and their fraction fields. -/
instance normalization_isIntegralClosure :
    IsIntegralClosure (NormalizationRing k) (nodeRing k) (RationalFunctions k) := by
  constructor
  · intro x y h
    apply Prod.ext
    · exact IsFractionRing.injective k[X] (FractionRing k[X]) (congrArg Prod.fst h)
    · exact IsFractionRing.injective k[X] (FractionRing k[X]) (congrArg Prod.snd h)
  · intro z
    constructor
    · intro hz
      have hl : _root_.IsIntegral k[X] z.1 :=
        IsIntegral.map_of_comp_eq
          ((RingHom.fst k[X] k[X]).comp (nodeRing k).val.toRingHom)
          (RingHom.fst (FractionRing k[X]) (FractionRing k[X])) rfl hz
      have hr : _root_.IsIntegral k[X] z.2 :=
        IsIntegral.map_of_comp_eq
          ((RingHom.snd k[X] k[X]).comp (nodeRing k).val.toRingHom)
          (RingHom.snd (FractionRing k[X]) (FractionRing k[X])) rfl hz
      obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp hl
      obtain ⟨q, hq⟩ := IsIntegrallyClosed.isIntegral_iff.mp hr
      exact ⟨(p, q), Prod.ext hp hq⟩
    · rintro ⟨z, rfl⟩
      exact IsIntegral.map_of_comp_eq (RingHom.id (nodeRing k)) (fractionMap k) rfl
        (Algebra.IsIntegral.isIntegral (R := nodeRing k) z)

theorem conductorPolynomial_ne_zero : (X * (X - 1) : k[X]) ≠ 0 :=
  mul_ne_zero X_ne_zero (by simpa only [C_1] using X_sub_C_ne_zero (1 : k))

/-- Regular elements of A are exactly pairs nonzero on both components. -/
theorem node_nonZeroDivisors_iff (a : nodeRing k) :
    a ∈ nonZeroDivisors (nodeRing k) ↔
      (a : NormalizationRing k).1 ≠ 0 ∧ (a : NormalizationRing k).2 ≠ 0 := by
  constructor
  · intro ha
    constructor
    · intro h
      have hz : conductorMul k (1, 0) * a = 0 := by
        apply Subtype.ext
        apply Prod.ext <;> simp [conductorMul, h]
      have hc := (mem_nonZeroDivisors_iff_right.mp ha) _ hz
      have hc' := congrArg (fun b : nodeRing k => (b : NormalizationRing k).1) hc
      exact conductorPolynomial_ne_zero k (by simpa [conductorMul] using hc')
    · intro h
      have hz : conductorMul k (0, 1) * a = 0 := by
        apply Subtype.ext
        apply Prod.ext <;> simp [conductorMul, h]
      have hc := (mem_nonZeroDivisors_iff_right.mp ha) _ hz
      have hc' := congrArg (fun b : nodeRing k => (b : NormalizationRing k).2) hc
      exact conductorPolynomial_ne_zero k (by simpa [conductorMul] using hc')
  · rintro ⟨hl, hr⟩
    apply mem_nonZeroDivisors_iff_right.mpr
    intro b hb
    apply Subtype.ext
    apply Prod.ext
    · have he := congrArg (fun c : nodeRing k => (c : NormalizationRing k).1) hb
      exact (mul_eq_zero.mp he).resolve_right hl
    · have he := congrArg (fun c : nodeRing k => (c : NormalizationRing k).2) hb
      exact (mul_eq_zero.mp he).resolve_right hr

/-- Clearing both component denominators with the conductor proves this is
literally the total ring of fractions of the two-node coordinate ring. -/
instance sameFractionRing : IsFractionRing (nodeRing k) (RationalFunctions k) where
  map_units a := by
    have ha := (node_nonZeroDivisors_iff k a).mp a.property
    apply Prod.isUnit_iff.mpr
    constructor
    · apply isUnit_iff_ne_zero.mpr
      exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (FractionRing k[X]))).mpr ha.1
    · apply isUnit_iff_ne_zero.mpr
      exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (FractionRing k[X]))).mpr ha.2
  surj z := by
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors k[X]) z.1
    obtain ⟨⟨c, d⟩, hcd⟩ := IsLocalization.surj (nonZeroDivisors k[X]) z.2
    let denominator : nodeRing k := diagonal k (X * (X - 1) * (b : k[X]) * (d : k[X]))
    have hd : denominator ∈ nonZeroDivisors (nodeRing k) := by
      apply (node_nonZeroDivisors_iff k denominator).mpr
      have hb : (b : k[X]) ≠ 0 := nonZeroDivisors.ne_zero b.property
      have hd : (d : k[X]) ≠ 0 := nonZeroDivisors.ne_zero d.property
      exact ⟨mul_ne_zero (mul_ne_zero (conductorPolynomial_ne_zero k) hb) hd,
        mul_ne_zero (mul_ne_zero (conductorPolynomial_ne_zero k) hb) hd⟩
    refine ⟨(conductorMul k (a * (d : k[X]), c * (b : k[X])), ⟨denominator, hd⟩), ?_⟩
    apply Prod.ext
    · change z.1 * algebraMap k[X] (FractionRing k[X]) (X * (X - 1) * (b : k[X]) * (d : k[X])) =
        algebraMap k[X] (FractionRing k[X]) (X * (X - 1) * (a * (d : k[X])))
      simp only [map_mul]
      calc
        _ = (z.1 * algebraMap k[X] (FractionRing k[X]) b) *
            algebraMap k[X] (FractionRing k[X]) X *
            algebraMap k[X] (FractionRing k[X]) (X - 1) *
            algebraMap k[X] (FractionRing k[X]) d := by ring
        _ = _ := by rw [hab]; ring
    · change z.2 * algebraMap k[X] (FractionRing k[X]) (X * (X - 1) * (b : k[X]) * (d : k[X])) =
        algebraMap k[X] (FractionRing k[X]) (X * (X - 1) * (c * (b : k[X])))
      simp only [map_mul]
      calc
        _ = (z.2 * algebraMap k[X] (FractionRing k[X]) d) *
            algebraMap k[X] (FractionRing k[X]) X *
            algebraMap k[X] (FractionRing k[X]) (X - 1) *
            algebraMap k[X] (FractionRing k[X]) b := by ring
        _ = _ := by rw [hcd]; ring
  exists_of_eq {a b} h := by
    have he : a = b := by
      apply Subtype.ext
      apply Prod.ext
      · exact IsFractionRing.injective k[X] (FractionRing k[X]) (congrArg Prod.fst h)
      · exact IsFractionRing.injective k[X] (FractionRing k[X]) (congrArg Prod.snd h)
    exact ⟨1, by simpa using he⟩

end AlgebraicGeometry.Scheme.TwoGon.Affine
