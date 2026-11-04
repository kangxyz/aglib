/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct
public import Aglib.Algebra.Homology.TotalComplex.FirstQuadrant

/-! # Evaluate the total map of the given degreewise cup products -/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

namespace DirectSum

variable {R : Type*} [Field R] {M N P : ℕ → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ j, AddCommMonoid (N j)] [∀ j, Module R (N j)]
  [∀ n, AddCommMonoid (P n)] [∀ n, Module R (P n)]

/-- The canonical tensor distribution on the actual total-degree fibers. -/
def totalDegreeSourceEquiv :
    ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ n, ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2 :=
  tensorFiberEquiv (R := R) M N
    (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- The supplied cup maps on the original summands of one total degree. -/
def cupFiberMap
    (e : ∀ p q n : ℕ, p + q = n → M p →ₗ[R] N q →ₗ[R] P n) (n : ℕ) :
    (⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2) →ₗ[R] P n :=
  DirectSum.toModule R _ _
    (fun s : HomologicalComplex₂.TotalDegree n =>
      TensorProduct.lift (e s.val.1 s.val.2 n s.property))

/-- Sum the original cup maps after the supplied total source equivalence. -/
def mapAfterEquivOfCup
    (E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ n, ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2)
    (e : ∀ p q n : ℕ, p + q = n → M p →ₗ[R] N q →ₗ[R] P n) :
    ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ n, P n :=
  mapAfterEquiv E (cupFiberMap e)

/-- The total cup map factors through the given presentation of its degree maps. -/
theorem mapAfterEquivOfCup_factorization
    (E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ n, ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2)
    (e : ∀ p q n : ℕ, p + q = n → M p →ₗ[R] N q →ₗ[R] P n)
    (G : ∀ n,
      (⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2) →ₗ[R] P n)
    (hG : ∀ n, G n = cupFiberMap e n)
    (L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ n, P n)
    (hL : L = mapAfterEquivOfCup E e) :
    MapFactorization L E G := by
  subst L
  rw [funext hG]
  exact mapAfterEquiv_factorization E (cupFiberMap e)

/-- The total cup map evaluates on the original homogeneous tensor and its chosen fiber. -/
theorem mapAfterEquivOfCup_tmul
    {E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ n, ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2}
    (hE : E = tensorFiberEquiv (R := R) M N
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (e : ∀ p q n : ℕ, p + q = n → M p →ₗ[R] N q →ₗ[R] P n)
    {L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ n, P n}
    (hL : L = mapAfterEquivOfCup E e)
    {p q n : ℕ} (h : p + q = n) (x : M p) (y : N q) :
    L (lof R ℕ M p x ⊗ₜ[R] lof R ℕ N q y) = lof R ℕ P n (e p q n h x y) := by
  subst n
  subst L
  subst E
  let F (n : ℕ) := ⨁ s : HomologicalComplex₂.TotalDegree n, M s.val.1 ⊗[R] N s.val.2
  let G (n : ℕ) : F n →ₗ[R] P n := cupFiberMap e n
  let v : F (p + q) := lof R _ _ ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y)
  let π := ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
  have hSource : @Eq (⨁ n, F n)
      (tensorFiberEquiv (R := R) M N π (lof R ℕ M p x ⊗ₜ[R] lof R ℕ N q y))
      (lof R ℕ F (p + q) v) :=
    tensorFiberEquiv_lof_tmul_lof (R := R) M N π p q x y
  calc
    _ = _ := mapAfterEquiv_apply _ G _
    _ = _ := congrArg (lmap G) hSource
    _ = _ := lmap_lof G _ _
    _ = _ := by
      dsimp only [G, v, cupFiberMap]
      rw [DirectSum.toModule_lof, TensorProduct.lift.tmul]

end DirectSum
