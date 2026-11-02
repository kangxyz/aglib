/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.AwayAlgebra
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.FieldPoints
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Coordinate
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.SMulRegular
public import Aglib.RingTheory.Regular.PrimeAvoidance
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Linear hyperplanes through a rational point

The coefficients of a hyperplane through the vector `a` belong to the kernel of the
actual linear evaluation `c ↦ ∑ cⱼ aⱼ`. On a chart containing that rational point,
the differences `Xⱼ/Xᵢ - aⱼ/aᵢ` separate its maximal ideal from every other prime.
On a chart not containing the point, `Xᵢ` itself is an allowed hyperplane and is a
unit in the chart frame. Thus finite associated-prime avoidance applies to this
constrained, original linear system, including for nonreduced modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (k : Type u) [Field k] (ι : Type u)

/-- Evaluation of the native standard chart at the ratios of a field vector.
For `a i ≠ 0`, this is the chart homomorphism of the rational projective point `a`. -/
def coordinateRingEvaluate (a : ι → k) (i : ι) : coordinateRing k ι i →+* k :=
  (MvPolynomial.eval₂Hom (RingHom.id k) (fun j : {j : ι // j ≠ i} => a j / a i)).comp
    (coordinateRingToPolynomial k ι i)

@[simp]
theorem coordinateRingEvaluate_coefficient (a : ι → k) (i : ι) (c : k) :
    coordinateRingEvaluate k ι a i (coordinateRingCoefficient k ι i c) = c := by
  simp [coordinateRingEvaluate]

@[simp]
theorem coordinateRingEvaluate_ratio (a : ι → k) (i : ι) (hi : a i ≠ 0) (j : ι) :
    coordinateRingEvaluate k ι a i (coordinateRatio k ι i j) = a j / a i := by
  by_cases h : j = i
  · subst j
    simp [hi]
  · change coordinateRingEvaluate k ι a i (coordinateRatio k ι i (⟨j, h⟩ : {j // j ≠ i})) = _
    rw [coordinateRingEvaluate, RingHom.comp_apply,
      coordinateRingToPolynomial_ratio k ι i ⟨j, h⟩]
    simp

/-- A prime different from a rational-point ideal misses one of the original
coordinate differences. No reducedness or algebraic closure is used. -/
theorem exists_coordinateRatio_sub_notMem (i : ι)
    (φ : coordinateRing k ι i →+* k)
    (hφ : ∀ c, φ (coordinateRingCoefficient k ι i c) = c)
    (P : Ideal (coordinateRing k ι i)) (hP : P.IsPrime)
    (hne : P ≠ RingHom.ker φ) :
    ∃ j, coordinateRatio k ι i j -
      coordinateRingCoefficient k ι i (φ (coordinateRatio k ι i j)) ∉ P := by
  by_contra! h
  let q := Ideal.Quotient.mk P
  have he : q.comp (polynomialToCoordinateRing k ι i) =
      ((q.comp (coordinateRingCoefficient k ι i)).comp φ).comp
        (polynomialToCoordinateRing k ι i) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_C, hφ]
    · intro j
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_X]
      exact sub_eq_zero.mp (by simpa only [map_sub] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr (h j.1)))
  have hle : RingHom.ker φ ≤ P := by
    intro z hz
    have hz' : φ z = 0 := hz
    have hzq := RingHom.congr_fun he (coordinateRingToPolynomial k ι i z)
    have hinv := RingHom.congr_fun
      (polynomialToCoordinateRing_comp_coordinateRingToPolynomial k ι i) z
    simp only [RingHom.comp_apply, RingHom.id_apply] at hinv
    simp only [RingHom.comp_apply, hinv, hz', map_zero] at hzq
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzq
  have hm : (RingHom.ker φ).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective φ (fun c => ⟨coordinateRingCoefficient k ι i c, hφ c⟩)
  exact hne (hm.eq_of_le hP.ne_top hle).symm

/-- On every chart, the genuine linear system of hyperplanes through a rational
point separates every prime other than that point. The exclusion is needed only
on charts where the point lies. -/
theorem exists_linearForm_through_notMem (a : ι → k) (i : ι)
    (P : Ideal (coordinateRing k ι i)) (hP : P.IsPrime)
    (hne : a i ≠ 0 → P ≠ RingHom.ker (coordinateRingEvaluate k ι a i)) :
    ∃ c : ι →₀ k, Finsupp.linearCombination k a c = 0 ∧
      Finsupp.linearCombination k (coordinateRatio k ι i) c ∉ P := by
  classical
  by_cases hi : a i = 0
  · refine ⟨Finsupp.single i 1, ?_, ?_⟩
    · simp [hi]
    · simpa only [Finsupp.linearCombination_single, one_smul, coordinateRatio_self] using
        (Ideal.ne_top_iff_one P).mp hP.ne_top
  · obtain ⟨j, hj⟩ := exists_coordinateRatio_sub_notMem k ι i
      (coordinateRingEvaluate k ι a i) (coordinateRingEvaluate_coefficient k ι a i)
      P hP (hne hi)
    refine ⟨Finsupp.single j 1 - Finsupp.single i (a j / a i), ?_, ?_⟩
    · simp only [map_sub, Finsupp.linearCombination_single, smul_eq_mul, one_mul]
      rw [div_mul_cancel₀ _ hi, sub_self]
    · simpa only [map_sub, Finsupp.linearCombination_single, one_smul,
        coordinateRatio_self, smul_eq_algebraMap_mul, mul_one,
        algebraMap_coordinateRing, coordinateRingEvaluate_ratio k ι a i hi] using hj

/-- Simultaneously regular original linear hyperplanes through a rational point.
The modules are allowed to have nilpotents and embedded associated primes; the
only incidence requirement is that the chosen point is not an associated point.
The regular elements are exactly the original coefficients `∑ cⱼ Xⱼ/Xᵢ`. -/
theorem exists_linearForm_through_isSMulRegular [Infinite k] [Finite ι]
    {J : Type*} [Finite J] (a : ι → k)
    (M : ι × J → Type*) [∀ p, AddCommGroup (M p)]
    [∀ p, Module (coordinateRing k ι p.1) (M p)]
    [∀ p, Module.Finite (coordinateRing k ι p.1) (M p)]
    (ha : ∀ (p : ι × J), a p.1 ≠ 0 →
      RingHom.ker (coordinateRingEvaluate k ι a p.1) ∉
        associatedPrimes (coordinateRing k ι p.1) (M p)) :
    ∃ c : ι →₀ k, Finsupp.linearCombination k a c = 0 ∧
      ∀ p : ι × J, IsSMulRegular (M p)
        (Finsupp.linearCombination k (coordinateRatio k ι p.1) c) := by
  let V := LinearMap.ker (Finsupp.linearCombination k a)
  let : ∀ p : ι × J, IsNoetherianRing (coordinateRing k ι p.1) := fun p =>
    isNoetherianRing_of_ringEquiv _ (coordinateRingEquivPolynomial k ι p.1).symm
  let lam : ∀ p : ι × J, V →ₗ[k] coordinateRing k ι p.1 := fun p =>
    (Finsupp.linearCombination k (coordinateRatio k ι p.1)).comp V.subtype
  obtain ⟨c, hc⟩ := associatedPrimes.exists_forall_isSMulRegular (V := V)
    (fun p : ι × J => coordinateRing k ι p.1) M lam (fun p P hP => by
      obtain ⟨c, hca, hcP⟩ := exists_linearForm_through_notMem k ι a p.1 P hP.isPrime
        (fun hi he => ha p hi (he ▸ hP))
      exact ⟨(⟨c, hca⟩ : V), hcP⟩)
  exact ⟨c.val, c.property, hc⟩

/-- Degree-one homogeneous polynomials from their actual finitely supported coefficients. -/
def linearFormPolynomial : (ι →₀ k) →ₗ[k] homogeneousSubmodule ι k 1 :=
  Finsupp.linearCombination k (fun j => ⟨X j, isHomogeneous_X k j⟩)

/-- The original homogeneous fraction, with its coefficient-linear structure. -/
def homogeneousChartFractionLinear (n : ℕ) (i : ι) :
    homogeneousSubmodule ι k n →ₗ[k] coordinateRing k ι i where
  toFun p := homogeneousChartFraction k ι n p i
  map_add' p q := by
    apply (coordinateRingEquivPolynomial k ι i).injective
    change coordinateRingToPolynomial k ι i _ = coordinateRingToPolynomial k ι i _
    simp only [homogeneousChartFraction, coordinateRingToPolynomial_mk, map_add,
      Submodule.coe_add]
  map_smul' c p := by
    apply (coordinateRingEquivPolynomial k ι i).injective
    change coordinateRingToPolynomial k ι i _ = coordinateRingToPolynomial k ι i _
    rw [smul_eq_algebraMap_mul, map_mul, algebraMap_coordinateRing,
      coordinateRingToPolynomial_coefficient]
    simp only [homogeneousChartFraction, coordinateRingToPolynomial_mk,
      Submodule.coe_smul_of_tower, MvPolynomial.smul_eq_C_mul, map_mul, dehomogenize_C,
      RingHom.id_apply]

/-- The original degree-one polynomial has precisely the expected chart coefficients. -/
theorem homogeneousChartFraction_linearForm (c : ι →₀ k) (i : ι) :
    homogeneousChartFraction k ι 1 (linearFormPolynomial k ι c) i =
      Finsupp.linearCombination k (coordinateRatio k ι i) c := by
  change homogeneousChartFractionLinear k ι 1 i (linearFormPolynomial k ι c) = _
  rw [linearFormPolynomial, Finsupp.apply_linearCombination]
  rfl

/-- The actual global twist section of a linear form, not an abstract section witness. -/
def linearFormSection (c : ι →₀ k) :
    (twistingSheaf k ι ((1 : ℕ) : ℤ)).val.obj (op ⊤) :=
  homogeneousSection k ι 1 (linearFormPolynomial k ι c)

set_option backward.isDefEq.respectTransparency false in
/-- Its original frame coefficient is the native chart-ring linear form. -/
theorem frameCoefficient_linearFormSection (c : ι →₀ k) (i : ι) :
    frameCoefficient k ι (linearFormSection k ι c) i le_rfl =
      Proj.awayToSection (homogeneousSubmodule ι k) (X i)
        (Finsupp.linearCombination k (coordinateRatio k ι i) c) := by
  change twistingSectionsEquiv k ι ((1 : ℕ) : ℤ) i le_rfl
    ((twistingSheaf k ι ((1 : ℕ) : ℤ)).val.map (homOfLE le_top).op
      (homogeneousSection k ι 1 (linearFormPolynomial k ι c))) = _
  rw [homogeneousSection_local]
  exact congrArg (fun z : coordinateRing k ι i =>
    Proj.awayToSection (homogeneousSubmodule ι k) (X i) z)
      (homogeneousChartFraction_linearForm k ι c i)

/-- Evaluation of the same native chart linear form is evaluation of its original
coefficient vector, divided by the chosen nonzero coordinate. -/
theorem coordinateRingEvaluate_linearForm (a : ι → k) (i : ι) (hi : a i ≠ 0)
    (c : ι →₀ k) :
    coordinateRingEvaluate k ι a i
      (Finsupp.linearCombination k (coordinateRatio k ι i) c) =
        Finsupp.linearCombination k a c / a i := by
  let e : coordinateRing k ι i →ₐ[k] k :=
    { __ := coordinateRingEvaluate k ι a i
      commutes' := coordinateRingEvaluate_coefficient k ι a i }
  rw [show coordinateRingEvaluate k ι a i _ = e.toLinearMap _ from rfl,
    Finsupp.apply_linearCombination]
  have heval (j : ι) : e (coordinateRatio k ι i j) = a j / a i :=
    coordinateRingEvaluate_ratio k ι a i hi j
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Function.comp_apply,
    AlgHom.toLinearMap_apply, heval,
    smul_eq_mul, div_eq_mul_inv, Finset.sum_mul, mul_assoc]

/-- The native chart-ring/sections isomorphism, retaining `Proj.awayToSection` as forward map. -/
def coordinateRingEquivSections (i : ι) :
    coordinateRing k ι i ≃+* Γ(ProjectiveSpace k ι, coordinateOpen k ι i) :=
  (Proj.basicOpenIsoAway (homogeneousSubmodule ι k) (X i)
    (isHomogeneous_X k i) Nat.zero_lt_one).commRingCatIsoToRingEquiv

/-- Evaluation of actual chart functions at the rational chart point. -/
def coordinateSectionEvaluate (a : ι → k) (i : ι) :
    Γ(ProjectiveSpace k ι, coordinateOpen k ι i) →+* k :=
  (coordinateRingEvaluate k ι a i).comp (coordinateRingEquivSections k ι i).symm.toRingHom

/-- The incidence equation vanishes on the original section in the rational chart frame. -/
theorem coordinateSectionEvaluate_frameCoefficient (a : ι → k) (i : ι) (hi : a i ≠ 0)
    (c : ι →₀ k) (hc : Finsupp.linearCombination k a c = 0) :
    coordinateSectionEvaluate k ι a i
      (frameCoefficient k ι (linearFormSection k ι c) i le_rfl) = 0 := by
  rw [frameCoefficient_linearFormSection]
  change coordinateRingEvaluate k ι a i
    ((coordinateRingEquivSections k ι i).symm
      ((coordinateRingEquivSections k ι i) _)) = 0
  rw [RingEquiv.symm_apply_apply, coordinateRingEvaluate_linearForm k ι a i hi, hc, zero_div]

set_option backward.isDefEq.respectTransparency false in
/-- A genuine global linear section through a rational point, regular on each of
finitely many coherent modules. The excluded prime is the actual chart evaluation
kernel, not an arbitrary closed-point linear evaluation kernel. -/
theorem exists_linearFormSection_through_isSMulRegular [Infinite k] [Finite ι]
    {J : Type*} [Finite J] (a : ι → k)
    (F : J → (ProjectiveSpace k ι).Modules)
    (hF : ∀ j, Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (ProjectiveSpace k ι) (F j))
    (ha : ∀ (j : J) (i : ι), a i ≠ 0 →
      RingHom.ker (coordinateSectionEvaluate k ι a i) ∉
        associatedPrimes Γ(ProjectiveSpace k ι, coordinateOpen k ι i)
          Γ(F j, coordinateOpen k ι i)) :
    ∃ c : ι →₀ k, Finsupp.linearCombination k a c = 0 ∧
      ∀ (j : J) (i : ι) (U : (ProjectiveSpace k ι).Opens) (hU : U ≤ coordinateOpen k ι i),
        IsSMulRegular Γ(F j, U) (frameCoefficient k ι (linearFormSection k ι c) i hU) := by
  let V := LinearMap.ker (Finsupp.linearCombination k a)
  let E := coordinateRingEquivSections k ι
  let : ∀ p : ι × J, Algebra k Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1) := fun p =>
    ((E p.1).toRingHom.comp (coordinateRingCoefficient k ι p.1)).toAlgebra
  let q : ∀ p : ι × J, coordinateRing k ι p.1 →ₐ[k]
      Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1) := fun p =>
    { __ := (E p.1).toRingHom
      commutes' := fun _ => rfl }
  let : ∀ p : ι × J, IsNoetherianRing Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1) :=
    fun p => IsLocallyNoetherian.component_noetherian ⟨_, isAffineOpen_coordinateOpen k ι p.1⟩
  let : ∀ p : ι × J, Module.Finite Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1)
      Γ(F p.2, coordinateOpen k ι p.1) := fun p =>
    Scheme.Modules.QuasiCoherent.finite_sections_of_affineLocallyFiniteType (F p.2) (hF p.2)
      ⟨_, isAffineOpen_coordinateOpen k ι p.1⟩
  let lam : ∀ p : ι × J, V →ₗ[k] Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1) := fun p =>
    (q p).toLinearMap.comp
      ((Finsupp.linearCombination k (coordinateRatio k ι p.1)).comp V.subtype)
  obtain ⟨c, hc⟩ := associatedPrimes.exists_forall_isSMulRegular (V := V)
    (fun p : ι × J => Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1))
    (fun p : ι × J => Γ(F p.2, coordinateOpen k ι p.1)) lam (fun p P hP => by
      have : P.IsPrime := hP.isPrime
      obtain ⟨c, hca, hcP⟩ := exists_linearForm_through_notMem k ι a p.1
        (P.comap (E p.1).toRingHom) inferInstance (fun hi he => by
          have he' : P = RingHom.ker (coordinateSectionEvaluate k ι a p.1) := by
            ext z
            have hz := SetLike.ext_iff.mp he ((E p.1).symm z)
            change (E p.1) ((E p.1).symm z) ∈ P ↔
              coordinateRingEvaluate k ι a p.1 ((E p.1).symm z) = 0 at hz
            change z ∈ P ↔
              coordinateRingEvaluate k ι a p.1 ((E p.1).symm z) = 0
            simpa only [RingEquiv.apply_symm_apply] using hz
          exact ha p.2 p.1 hi (he' ▸ hP))
      exact ⟨(⟨c, hca⟩ : V), hcP⟩)
  refine ⟨c.val, c.property, fun j i U hU => ?_⟩
  have hchart := hc (i, j)
  change IsSMulRegular Γ(F j, coordinateOpen k ι i)
    ((E i) (Finsupp.linearCombination k (coordinateRatio k ι i) c.val)) at hchart
  have hA := isAffineOpen_coordinateOpen k ι i
  let : ((F j).restrict hA.fromSpec).IsQuasicoherent := (hF j _ hA.fromSpec).1
  rw [frameCoefficient_eq_map, frameCoefficient_linearFormSection]
  exact Scheme.Modules.QuasiCoherent.AffineOpenSections.isSMulRegular_restrict
    (F j) hA hchart hU

/-- Every nonzero-coordinate chart evaluation describes the same original rational
projective point. The normalization rescales its vector; it does not replace the point. -/
theorem coordinateRingEvaluate_point [Finite ι] (a : ι → k) (i : ι) (hi : a i ≠ 0) :
    BinaryFormProduct.Field.point (RingHom.id k) a i hi =
      Spec.map (CommRingCat.ofHom (coordinateRingEvaluate k ι a i)) ≫
        Proj.awayι (homogeneousSubmodule ι k) (X i) (isHomogeneous_X k i) Nat.zero_lt_one := by
  let b : ι → k := fun j => a j / a i
  have hb : b i ≠ 0 := by simp [b, hi]
  have he : BinaryFormProduct.Field.point (RingHom.id k) a i hi =
      BinaryFormProduct.Field.point (RingHom.id k) b i hb :=
    BinaryFormProduct.Field.point_eq_of_scale (RingHom.id k) a b i i hi hb
      (a i)⁻¹ (inv_ne_zero hi) (fun j => by dsimp [b]; rw [div_eq_mul_inv, mul_comm])
  exact he.trans (BinaryFormProduct.Field.point_eq_chart_of_values (RingHom.id k) b i hb
    (coordinateRingEvaluate k ι a i) (coordinateRingEvaluate_coefficient k ι a i)
    (fun j => (coordinateRingEvaluate_ratio k ι a i hi j).symm))

/-- The regular constrained section makes the original twisting multiplication
monic on every specified coherent module. -/
theorem exists_linearFormSection_through_mono [Infinite k] [Finite ι]
    {J : Type*} [Finite J] (a : ι → k)
    (F : J → (ProjectiveSpace k ι).Modules)
    (hF : ∀ j, Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (ProjectiveSpace k ι) (F j))
    (ha : ∀ (j : J) (i : ι), a i ≠ 0 →
      RingHom.ker (coordinateSectionEvaluate k ι a i) ∉
        associatedPrimes Γ(ProjectiveSpace k ι, coordinateOpen k ι i)
          Γ(F j, coordinateOpen k ι i)) :
    ∃ c : ι →₀ k, Finsupp.linearCombination k a c = 0 ∧
      ∀ j : J, Mono ((twistingTensorZeroIso k ι).inv.app (F j) ≫
        (twistingTensorMultiply k ι ((1 : ℕ) : ℤ) 0 (linearFormSection k ι c)).app (F j)) := by
  obtain ⟨c, hc, hreg⟩ := exists_linearFormSection_through_isSMulRegular k ι a F hF ha
  exact ⟨c, hc, fun j => mono_twistingTensorMultiply_of_isSMulRegular k ι
    (linearFormSection k ι c) (F j) (hreg j)⟩

end AlgebraicGeometry.ProjectiveSpace

namespace IsSMulRegular

/-- A regular element in the maximal ideal of an actual localized module
excludes the corresponding original associated prime. Neither Noetherianity nor
finite generation is needed for this direction. -/
theorem not_mem_associatedPrimes_of_isLocalizedModule_atPrime
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal R) [P.IsPrime] [IsLocalization P.primeCompl S] [IsLocalRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) [IsLocalizedModule P.primeCompl f]
    {a : S} (hreg : IsSMulRegular N a) (ha : a ∈ IsLocalRing.maximalIdeal S) :
    P ∉ associatedPrimes R M := by
  intro hP
  have h : IsAssociatedPrime (IsLocalRing.maximalIdeal S) N :=
    Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      P.primeCompl f (IsLocalRing.maximalIdeal S) (by
        change (IsLocalRing.maximalIdeal S).under R ∈ associatedPrimes R M
        rw [IsLocalization.AtPrime.under_maximalIdeal S P]
        exact hP)
  obtain ⟨y, hy⟩ := h.2
  have hy0 : y ≠ 0 := by
    intro hzero
    apply h.isPrime.ne_top
    rw [hzero, Submodule.colon_singleton_zero, Ideal.radical_top] at hy
    exact hy
  rw [hy, Ideal.mem_radical_iff] at ha
  obtain ⟨n, hn⟩ := ha
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hn
  exact hy0 ((IsSMulRegular.pow n hreg).right_eq_zero_of_smul hn)

end IsSMulRegular
