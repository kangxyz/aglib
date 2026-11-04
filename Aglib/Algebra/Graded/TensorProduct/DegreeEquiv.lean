/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct.TotalValues

/-! # Totalization of the given degreewise bijections -/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

namespace LinearEquiv

variable {R A B : Type*} [Field R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]

/-- Use the given forward map with the already chosen inverse. -/
def withGivenForward (q : A ≃ₗ[R] B) (f : A →ₗ[R] B) (h : q.toLinearMap = f) :
    A ≃ₗ[R] B where
  toFun := f
  invFun := q.symm
  left_inv := fun x => by
    rw [← h]
    exact q.symm_apply_apply x
  right_inv := fun y => by
    rw [← h]
    exact q.apply_symm_apply y
  map_add' := f.map_add
  map_smul' := f.map_smul

end LinearEquiv

namespace DirectSum

variable {R : Type*} [Field R] {M N P : ℕ → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ j, AddCommMonoid (N j)] [∀ j, Module R (N j)]
  [∀ n, AddCommMonoid (P n)] [∀ n, Module R (P n)]

variable (G : ∀ n,
    (⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2) →ₗ[R] P n)
  (hG : ∀ n, Function.Bijective (G n))

/-- The equivalence of the given bijective degree map. -/
def degreeEquivOfBijective (n : ℕ) :=
  LinearEquiv.ofBijective (G n) (hG n)

/-- The chosen degree equivalence has the given map as its forward map. -/
theorem degreeEquivOfBijective_toLinearMap {n : ℕ}
    (Q : (⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2) ≃ₗ[R] P n)
    (hQ : Q = degreeEquivOfBijective G hG n) :
    Q.toLinearMap = G n := by
  subst Q
  rfl

/-- Totalize the same inverses after the given source distribution. -/
def totalEquivOfBijective
    (E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ n, ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2) :=
  equivAfterEquiv E (degreeEquivOfBijective G hG)

/-- The total forward map is the given factorized operator. -/
theorem totalEquivOfBijective_toLinearMap
    (E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ n, ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2)
    (Q : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R] ⨁ n, P n)
    (hQ : Q = totalEquivOfBijective G hG E)
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ n, P n)
    (hL : MapFactorization L E G) :
    Q.toLinearMap = L := by
  subst Q
  refine (equivAfterEquiv_toLinearMap_of E (degreeEquivOfBijective G hG) G ?_).trans ?_
  · exact fun _ => rfl
  · apply LinearMap.ext
    intro z
    exact (hL z).symm

/-- The original total inverse with the supplied factorized forward operator. -/
def totalEquivWithGivenForward
    (E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ n, ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2)
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ n, P n)
    (hL : MapFactorization L E G) :=
  let Q := totalEquivOfBijective G hG E
  Q.withGivenForward L (totalEquivOfBijective_toLinearMap G hG E Q rfl L hL)

end DirectSum

universe u m n p

namespace DirectSum

variable {R : Type u} [CommSemiring R]
  {M : ℕ → Type m} {N : ℕ → Type n}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ j, AddCommMonoid (N j)] [∀ j, Module R (N j)]

/-- Evaluate the original degree-one source support at one class before any
cohomology family or degreewise inverse is specialized. -/
theorem equivAfterEquiv_symm_degreeOne_apply_of_source
    {P : ℕ → Type p} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    (E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ d, ⨁ t : HomologicalComplex₂.TotalDegree d,
        M t.val.1 ⊗[R] N t.val.2)
    (hE : E = tensorFiberEquiv (R := R) M N
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (e : ∀ d, (⨁ t : HomologicalComplex₂.TotalDegree d,
      M t.val.1 ⊗[R] N t.val.2) ≃ₗ[R] P d)
    (C : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R] ⨁ d, P d)
    (hC : C = equivAfterEquiv E e) (z : P 1) :
    TensorProduct.map
        (lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0)
        (lof R ℕ N 1 ∘ₗ DFinsupp.lapply 1)
        (C.symm (lof R ℕ P 1 z)) +
      TensorProduct.map
        (lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1)
        (lof R ℕ N 0 ∘ₗ DFinsupp.lapply 0)
        (C.symm (lof R ℕ P 1 z)) =
      C.symm (lof R ℕ P 1 z) := by
  subst C
  subst E
  have hSource := tensorFiberEquiv_symm_degreeOne (R := R) M N
    (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)) rfl
  have hWhole := equivAfterEquiv_symm_support
    (tensorFiberEquiv (R := R) M N
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    e 1
    (TensorProduct.map (lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0)
      (lof R ℕ N 1 ∘ₗ DFinsupp.lapply 1))
    (TensorProduct.map (lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1)
      (lof R ℕ N 0 ∘ₗ DFinsupp.lapply 0)) hSource
  have hValue := LinearMap.congr_fun hWhole z
  simp only [LinearMap.add_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap] at hValue
  exact hValue

end DirectSum
