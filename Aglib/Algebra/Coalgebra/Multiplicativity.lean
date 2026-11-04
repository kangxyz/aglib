/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Coalgebra.Comparison
public import Aglib.Algebra.Coalgebra.Graded.Primitive
public import Aglib.Algebra.Graded.ExternalProduct.SourceIdentity
public import Aglib.Algebra.Graded.DirectSum
public import Aglib.Algebra.Graded.TensorProduct
public import Aglib.Algebra.Graded.TensorProduct.SignedComparison
public import Aglib.Algebra.Homology.TotalComplex.FirstQuadrant

/-!
# Laws and degree-one bounds for a given coproduct

The property concerns the supplied linear coproduct and the function of the
same source identification. The inverse-comparison supplier uses the original
chosen inverse and original pullback; it constructs no additional algebra or
coalgebra model. The degree-one dimension transfer uses the same canonical
summand grading and original source identification.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

universe u a b s m p

namespace LinearMap

variable {R : Type u} [CommSemiring R]
  {A : Type a} [AddCommMonoid A] [Module R A] [Mul A]
  {S : Type s} [Mul S]

/-- The supplied coproduct is multiplicative after the supplied source function. -/
def IsMultiplicativeAfter (Δ : A →ₗ[R] A ⊗[R] A) (t : A ⊗[R] A → S) : Prop :=
  ∀ x y : A, t (Δ (x * y)) = t (Δ x) * t (Δ y)

/-- Evaluate the whole multiplicativity law at the original two elements. -/
theorem IsMultiplicativeAfter.apply
    {Δ : A →ₗ[R] A ⊗[R] A} {t : A ⊗[R] A → S}
    (h : IsMultiplicativeAfter Δ t) (x y : A) :
    t (Δ (x * y)) = t (Δ x) * t (Δ y) := h x y

end LinearMap

namespace LinearEquiv

/-- The original inverse comparison supplies multiplicativity of the specified
coproduct in the original target multiplication. -/
theorem isMultiplicativeAfter_of_algebra_comparison
    {R : Type u} [CommSemiring R]
    {A : Type a} [Semiring A] [Algebra R A]
    {B : Type b} [Semiring B] [Algebra R B]
    {S : Type s} [Semiring S] [Algebra R S]
    (C : A ⊗[R] A ≃ₗ[R] B) (t : A ⊗[R] A ≃ₗ[R] S) (Φ : S →ₐ[R] B)
    (hC : Φ.toLinearMap ∘ₗ t.toLinearMap = C.toLinearMap)
    (f : A →ₐ[R] B) (fLinear : A →ₗ[R] B) (hf : f.toLinearMap = fLinear)
    (Δ : A →ₗ[R] A ⊗[R] A) (hΔ : Δ = C.symm.toLinearMap ∘ₗ fLinear) :
    LinearMap.IsMultiplicativeAfter Δ t := by
  intro x y
  rw [hΔ, ← hf]
  exact inverse_mul_of_algebra_comparison C t Φ hC f x y

/-- The original comparison supplies injectivity of its algebra map and the
whole function equation for the specified inverse pullback. -/
theorem inverse_comparison_properties
    {R : Type u} [CommSemiring R]
    {A : Type a} [Semiring A] [Algebra R A]
    {B : Type b} [Semiring B] [Algebra R B]
    {S : Type s} [Semiring S] [Algebra R S]
    (C : A ⊗[R] A ≃ₗ[R] B) (t : A ⊗[R] A ≃ₗ[R] S) (Φ : S →ₐ[R] B)
    (hC : Φ.toLinearMap ∘ₗ t.toLinearMap = C.toLinearMap)
    (f : A →ₐ[R] B) (fLinear : A →ₗ[R] B) (hf : f.toLinearMap = fLinear)
    (Δ : A →ₗ[R] A ⊗[R] A) (hΔ : Δ = C.symm.toLinearMap ∘ₗ fLinear) :
    Function.Injective Φ ∧ ∀ a : A, Φ (t (Δ a)) = f a := by
  constructor
  · intro x y hxy
    apply t.symm.injective
    apply C.injective
    have hx := LinearMap.congr_fun hC (t.symm x)
    have hy := LinearMap.congr_fun hC (t.symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, AlgHom.toLinearMap_apply] at hx hy
    exact hx.symm.trans (hxy.trans hy)
  · intro a
    rw [hΔ, ← hf]
    exact apply_symm_of_algebra_comparison C t Φ hC (f a)

end LinearEquiv

namespace DirectSum

/-- Specialize the inverse comparison using the original signed equation at its given type. -/
theorem inverse_comparison_properties_of_signed
    {R : Type u} [CommRing R] {M : ℕ → Type m} {P : ℕ → Type p}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [GRing M] [GAlgebra R M] [GRing P] [GAlgebra R P]
    [GradedAlgebra (summandSubmodule (R := R) M)]
    {C : (DirectSum ℕ M ⊗[R] DirectSum ℕ M) ≃ₗ[R] DirectSum ℕ P}
    {t : (DirectSum ℕ M ⊗[R] DirectSum ℕ M) ≃ₗ[R]
      GradedTensorProduct R (summandSubmodule (R := R) M) (summandSubmodule (R := R) M)}
    {Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) M) →ₐ[R] DirectSum ℕ P}
    (hC : ExternalSignedTotalEq Φ t C.toLinearMap)
    (f : DirectSum ℕ M →ₐ[R] DirectSum ℕ P)
    (fLinear : DirectSum ℕ M →ₗ[R] DirectSum ℕ P) (hf : f.toLinearMap = fLinear)
    (Δ : DirectSum ℕ M →ₗ[R] DirectSum ℕ M ⊗[R] DirectSum ℕ M)
    (hΔ : Δ = C.symm.toLinearMap ∘ₗ fLinear) :
    Function.Injective Φ ∧ ∀ a : DirectSum ℕ M, Φ (t (Δ a)) = f a :=
  LinearEquiv.inverse_comparison_properties C t Φ hC f fLinear hf Δ hΔ

/-- The original homogeneous inverse law and degree-one pullback give support
in the canonical summand grading, without another chosen total inverse. -/
theorem comul_degreeOne_of_inverse_inclusion
    {R : Type u} [ringR : CommRing R]
    {M : ℕ → Type m} [groupM : ∀ i, AddCommGroup (M i)]
    [moduleM : ∀ i, Module R (M i)]
    [ringM : DirectSum.GRing M] [algebraM : DirectSum.GAlgebra R M]
    {P : ℕ → Type p} [groupP : ∀ i, AddCommGroup (P i)]
    [moduleP : ∀ i, Module R (P i)]
    {E : ((⨁ i, M i) ⊗[R] ⨁ j, M j) ≃ₗ[R]
      ⨁ d, ⨁ t : HomologicalComplex₂.TotalDegree d,
        M t.val.1 ⊗[R] M t.val.2}
    {C : ((⨁ i, M i) ⊗[R] ⨁ j, M j) ≃ₗ[R] ⨁ d, P d}
    {v : P 1 → ⨁ t : HomologicalComplex₂.TotalDegree 1,
      M t.val.1 ⊗[R] M t.val.2}
    (hInv : ∀ z, C.symm (DirectSum.homogeneousInclusion (R := R) P 1 z) =
      E.symm (DirectSum.lof R ℕ _ 1 (v z)))
    (hE : E = DirectSum.tensorFiberEquiv (R := R) M M
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (f : (⨁ i, M i) →ₗ[R] ⨁ d, P d) (f₁ : M 1 →ₗ[R] P 1)
    (hf : ∀ z, f (DirectSum.homogeneousInclusion (R := R) M 1 z) =
      DirectSum.homogeneousInclusion (R := R) P 1 (f₁ z))
    (Δ : (⨁ i, M i) →ₗ[R] (⨁ i, M i) ⊗[R] ⨁ j, M j)
    (hΔ : Δ = C.symm.toLinearMap ∘ₗ f)
    (x : DirectSum.summandSubmodule (R := R) M 1) :
    TensorProduct.map
        (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 0)
        (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 1)
        (Δ (x : ⨁ i, M i)) +
      TensorProduct.map
        (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 1)
        (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 0)
        (Δ (x : ⨁ i, M i)) = Δ (x : ⨁ i, M i) := by
  subst E
  obtain ⟨x, hx⟩ := x
  obtain ⟨z, rfl⟩ := hx
  have hπ (i : ℕ) :
      GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) i =
        DirectSum.lof R ℕ M i ∘ₗ DFinsupp.lapply i :=
    LinearMap.ext (DirectSum.proj_summandSubmodule (R := R) M i)
  rw [hπ 0, hπ 1, hΔ]
  change TensorProduct.map (DirectSum.lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0)
      (DirectSum.lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1)
      (C.symm (f (DirectSum.homogeneousInclusion (R := R) M 1 z))) +
    TensorProduct.map (DirectSum.lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1)
      (DirectSum.lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0)
      (C.symm (f (DirectSum.homogeneousInclusion (R := R) M 1 z))) =
    C.symm (f (DirectSum.homogeneousInclusion (R := R) M 1 z))
  rw [hf, hInv]
  have hSource := DirectSum.tensorFiberEquiv_symm_degreeOne (R := R) M M
    (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)) rfl
  have hValue := LinearMap.congr_fun hSource (v (f₁ z))
  let y := (DirectSum.tensorFiberEquiv (R := R) M M
    (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ))).symm
    (DirectSum.lof R ℕ _ 1 (v (f₁ z)))
  change TensorProduct.map (DirectSum.lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0)
      (DirectSum.lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1) y +
    TensorProduct.map (DirectSum.lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1)
      (DirectSum.lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0) y = y at hValue
  exact hValue

/-- Field-facing specialization of the same inverse-support law. Scalar and
module dictionaries are fixed while the families are still variable, so a
native field application retains its original selected maps and projections. -/
theorem comul_degreeOne_of_inverse_inclusion_field
    {R : Type u} [fieldR : Field R]
    {M : ℕ → Type m} [groupM : ∀ i, AddCommGroup (M i)]
    [moduleM : ∀ i, Module R (M i)]
    [ringM : DirectSum.GRing M] [algebraM : DirectSum.GAlgebra R M]
    {P : ℕ → Type p} [groupP : ∀ i, AddCommGroup (P i)]
    [moduleP : ∀ i, Module R (P i)]
    {E : ((⨁ i, M i) ⊗[R] ⨁ j, M j) ≃ₗ[R]
      ⨁ d, ⨁ t : HomologicalComplex₂.TotalDegree d,
        M t.val.1 ⊗[R] M t.val.2}
    {C : ((⨁ i, M i) ⊗[R] ⨁ j, M j) ≃ₗ[R] ⨁ d, P d}
    {v : P 1 → ⨁ t : HomologicalComplex₂.TotalDegree 1,
      M t.val.1 ⊗[R] M t.val.2}
    (hInv : ∀ z, C.symm (DirectSum.homogeneousInclusion (R := R) P 1 z) =
      E.symm (DirectSum.lof R ℕ _ 1 (v z)))
    (hE : E = DirectSum.tensorFiberEquiv (R := R) M M
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (f : (⨁ i, M i) →ₗ[R] ⨁ d, P d) (f₁ : M 1 →ₗ[R] P 1)
    (hf : ∀ z, f (DirectSum.homogeneousInclusion (R := R) M 1 z) =
      DirectSum.homogeneousInclusion (R := R) P 1 (f₁ z))
    (Δ : (⨁ i, M i) →ₗ[R] (⨁ i, M i) ⊗[R] ⨁ j, M j)
    (hΔ : Δ = C.symm.toLinearMap ∘ₗ f)
    (x : DirectSum.summandSubmodule (R := R) M 1) :
    TensorProduct.map
        (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 0)
        (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 1)
        (Δ (x : ⨁ i, M i)) +
      TensorProduct.map
        (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 1)
        (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 0)
        (Δ (x : ⨁ i, M i)) = Δ (x : ⨁ i, M i) := by
  exact comul_degreeOne_of_inverse_inclusion
    (ringR := @Field.toCommRing R fieldR)
    (M := M) (groupM := groupM) (moduleM := moduleM)
    (ringM := ringM) (algebraM := algebraM)
    (P := P) (groupP := groupP) (moduleP := moduleP)
    (E := E) (C := C) (v := v) hInv hE f f₁ hf Δ hΔ x

/-- Support in the two degree-one bidegrees for the supplied pullback
followed by the same chosen inverse, using the original summand projections. -/
def InversePullbackDegreeOneSupport
    {R : Type u} [fieldR : Field R]
    {M : ℕ → Type m} [groupM : ∀ i, AddCommGroup (M i)]
    [moduleM : ∀ i, Module R (M i)]
    [ringM : DirectSum.GRing M] [algebraM : DirectSum.GAlgebra R M]
    {P : ℕ → Type p} [groupP : ∀ i, AddCommGroup (P i)]
    [moduleP : ∀ i, Module R (P i)]
    (C : ((⨁ i, M i) ⊗[R] ⨁ j, M j) ≃ₗ[R] ⨁ d, P d)
    (f : (⨁ i, M i) →ₗ[R] ⨁ d, P d)
    (x : DirectSum.summandSubmodule (R := R) M 1) : Prop :=
  TensorProduct.map
      (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 0)
      (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 1)
      ((C.symm.toLinearMap ∘ₗ f) (x : ⨁ i, M i)) +
    TensorProduct.map
      (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 1)
      (GradedAlgebra.proj (DirectSum.summandSubmodule (R := R) M) 0)
      ((C.symm.toLinearMap ∘ₗ f) (x : ⨁ i, M i)) =
    (C.symm.toLinearMap ∘ₗ f) (x : ⨁ i, M i)

/-- The original homogeneous inverse law gives the transparent support
proposition for the specified pullback followed by that same chosen inverse. -/
theorem inverse_pullback_degreeOne_of_inverse_inclusion
    {R : Type u} [fieldR : Field R]
    {M : ℕ → Type m} [groupM : ∀ i, AddCommGroup (M i)]
    [moduleM : ∀ i, Module R (M i)]
    [ringM : DirectSum.GRing M] [algebraM : DirectSum.GAlgebra R M]
    {P : ℕ → Type p} [groupP : ∀ i, AddCommGroup (P i)]
    [moduleP : ∀ i, Module R (P i)]
    {E : ((⨁ i, M i) ⊗[R] ⨁ j, M j) ≃ₗ[R]
      ⨁ d, ⨁ t : HomologicalComplex₂.TotalDegree d,
        M t.val.1 ⊗[R] M t.val.2}
    {C : ((⨁ i, M i) ⊗[R] ⨁ j, M j) ≃ₗ[R] ⨁ d, P d}
    {v : P 1 → ⨁ t : HomologicalComplex₂.TotalDegree 1,
      M t.val.1 ⊗[R] M t.val.2}
    (hInv : ∀ z, C.symm (DirectSum.homogeneousInclusion (R := R) P 1 z) =
      E.symm (DirectSum.lof R ℕ _ 1 (v z)))
    (hE : E = DirectSum.tensorFiberEquiv (R := R) M M
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (f : (⨁ i, M i) →ₗ[R] ⨁ d, P d) (f₁ : M 1 →ₗ[R] P 1)
    (hf : ∀ z, f (DirectSum.homogeneousInclusion (R := R) M 1 z) =
      DirectSum.homogeneousInclusion (R := R) P 1 (f₁ z))
    (x : DirectSum.summandSubmodule (R := R) M 1) :
    InversePullbackDegreeOneSupport C f x := by
  exact comul_degreeOne_of_inverse_inclusion_field
    (fieldR := fieldR) (M := M) (groupM := groupM) (moduleM := moduleM)
    (ringM := ringM) (algebraM := algebraM)
    (P := P) (groupP := groupP) (moduleP := moduleP)
    (E := E) (C := C) (v := v) hInv hE f f₁ hf
    (C.symm.toLinearMap ∘ₗ f) rfl x

end DirectSum

namespace LinearEquiv

/-- The original comparison-function properties and the actual source unit
identify the unit value of the specified coproduct. -/
theorem comul_one_of_comparison_properties
    {R : Type u} [CommSemiring R]
    {A : Type a} [Semiring A] [Algebra R A]
    {B : Type b} [Semiring B] [Algebra R B]
    {S : Type s} [Semiring S] [Algebra R S]
    (t : A ⊗[R] A ≃ₗ[R] S) (Φ : S →ₐ[R] B) (f : A →ₐ[R] B)
    (Δ : A →ₗ[R] A ⊗[R] A)
    (h : Function.Injective Φ ∧ ∀ a : A, Φ (t (Δ a)) = f a)
    (ht : t ((1 : A) ⊗ₜ[R] (1 : A)) = 1) :
    Δ 1 = (1 : A) ⊗ₜ[R] (1 : A) := by
  apply t.injective
  apply h.1
  rw [ht]
  simpa only [map_one] using h.2 (1 : A)

end LinearEquiv

namespace LinearMap

/-- Multiplicativity follows from the same original comparison function and
its injectivity, without constructing another inverse or algebra map. -/
theorem isMultiplicativeAfter_of_comparison_properties
    {R : Type u} [CommSemiring R]
    {A : Type a} [Semiring A] [Algebra R A]
    {B : Type b} [Semiring B] [Algebra R B]
    {S : Type s} [Semiring S] [Algebra R S]
    (Φ : S →ₐ[R] B) (f : A →ₐ[R] B)
    (Δ : A →ₗ[R] A ⊗[R] A) (t : A ⊗[R] A → S)
    (h : Function.Injective Φ ∧ ∀ a : A, Φ (t (Δ a)) = f a) :
    IsMultiplicativeAfter Δ t := by
  intro a b
  apply h.1
  simp only [map_mul, h.2]

end LinearMap

namespace GradedAlgebra

private theorem finrank_degreeOne_le_of_multiplicative_comul
    {k : Type u} [Field k] {A : Type a} [Ring A] [Algebra k A] [Nontrivial A]
    {grade : ℕ → Submodule k A} [GradedAlgebra grade] [Coalgebra k A]
    [Module.Finite k (grade 1)]
    {t : A ⊗[k] A ≃ₗ[k] GradedTensorProduct k grade grade}
    (ht : t = GradedTensorProduct.of k grade grade)
    (hε : ∀ a, GradedAlgebra.proj grade 0 a = Coalgebra.counit (R := k) a • (1 : A))
    (hOne : Coalgebra.comul (R := k) (1 : A) = (1 : A) ⊗ₜ[k] (1 : A))
    (hMul : LinearMap.IsMultiplicativeAfter (Coalgebra.comul (R := k)) t)
    (hDegree : ∀ x : grade 1,
      TensorProduct.map (GradedAlgebra.proj grade 0) (GradedAlgebra.proj grade 1)
          (Coalgebra.comul (x : A)) +
        TensorProduct.map (GradedAlgebra.proj grade 1) (GradedAlgebra.proj grade 0)
          (Coalgebra.comul (x : A)) = Coalgebra.comul (x : A))
    (g : ℕ) (hVanish : ∀ n, g < n → grade n = ⊥) :
    Module.finrank k (grade 1) ≤ g := by
  apply finrank_degreeOne_le_of_comul_grading grade hε hOne ?_ hDegree g hVanish
  intro a b
  rw [← ht]
  exact hMul.apply a b

end GradedAlgebra

namespace DirectSum

/-- The original coproduct laws, augmentation and homogeneous vanishing give
an original degree-one dimension bound on the same direct-sum carrier.
All scalar, grading and coproduct structures are the supplied original ones. -/
theorem finrank_degreeOne_le_of_comul_grading
    {k : Type u} [Field k] {M : ℕ → Type m}
    [groupM : ∀ i, AddCommGroup (M i)] [moduleM : ∀ i, Module k (M i)]
    [ringM : GRing M] [algebraM : GAlgebra k M]
    [coalgebraM : Coalgebra k (DirectSum ℕ M)]
    [Nontrivial (DirectSum ℕ M)] [finiteOne : Module.Finite k (M 1)]
    {t : (DirectSum ℕ M ⊗[k] DirectSum ℕ M) →
      GradedTensorProduct k (summandSubmodule (R := k) M) (summandSubmodule (R := k) M)}
    (ε : DirectSum ℕ M →ₗ[k] k) (hε : Coalgebra.counit (R := k) = ε)
    (hZero : ∀ a : DirectSum ℕ M,
      GradedAlgebra.proj (summandSubmodule (R := k) M) 0 a = ε a • (1 : DirectSum ℕ M))
    (hOne : Coalgebra.comul (R := k) (1 : DirectSum ℕ M) =
      (1 : DirectSum ℕ M) ⊗ₜ[k] (1 : DirectSum ℕ M))
    (hMul : LinearMap.IsMultiplicativeAfter (Coalgebra.comul (R := k)) t)
    (ht : ∀ z, t z = externalProductSourceEquiv (R := k) (M := M) (N := M) z)
    (hDegree : ∀ x : summandSubmodule (R := k) M 1,
      TensorProduct.map
          (GradedAlgebra.proj (summandSubmodule (R := k) M) 0)
          (GradedAlgebra.proj (summandSubmodule (R := k) M) 1)
          (Coalgebra.comul (x : DirectSum ℕ M)) +
        TensorProduct.map
          (GradedAlgebra.proj (summandSubmodule (R := k) M) 1)
          (GradedAlgebra.proj (summandSubmodule (R := k) M) 0)
          (Coalgebra.comul (x : DirectSum ℕ M)) = Coalgebra.comul (x : DirectSum ℕ M))
    (g : ℕ) (hVanish : ∀ n, g < n → Subsingleton (M n)) :
    Module.finrank k (M 1) ≤ g := by
  let selected := externalProductSourceEquiv (R := k) (M := M) (N := M)
  have hMulSelected : LinearMap.IsMultiplicativeAfter (Coalgebra.comul (R := k)) selected := by
    intro a b
    exact (ht (Coalgebra.comul (a * b))).symm.trans
      ((hMul.apply a b).trans
        (congrArg₂ (· * ·) (ht (Coalgebra.comul a)) (ht (Coalgebra.comul b))))
  have hCounit (a : DirectSum ℕ M) :
      GradedAlgebra.proj (summandSubmodule (R := k) M) 0 a =
        Coalgebra.counit (R := k) a • (1 : DirectSum ℕ M) := by
    rw [hε]
    exact hZero a
  have hVanishGrade : ∀ n, g < n → summandSubmodule (R := k) M n = ⊥ := by
    intro n hn
    let : Subsingleton (M n) := hVanish n hn
    apply (Submodule.eq_bot_iff _).mpr
    intro a ha
    change ∃ x, homogeneousInclusion (R := k) M n x = a at ha
    obtain ⟨x, hx⟩ := ha
    have hZero := congrArg (homogeneousInclusion (R := k) M n) (Subsingleton.elim x 0)
    exact hx.symm.trans (hZero.trans (map_zero _))
  let : Module.Finite k (summandSubmodule (R := k) M 1) :=
    Module.Finite.equiv (summandLinearEquiv (R := k) M 1)
  have hSource := externalProductSourceEquiv_eq_of (R := k) (M := M) (N := M)
  have hBound := GradedAlgebra.finrank_degreeOne_le_of_multiplicative_comul
    (A := DirectSum ℕ M) (grade := summandSubmodule (R := k) M)
    hSource hCounit hOne hMulSelected hDegree g hVanishGrade
  exact (summandLinearEquiv (R := k) M 1).finrank_eq.trans_le hBound

end DirectSum
