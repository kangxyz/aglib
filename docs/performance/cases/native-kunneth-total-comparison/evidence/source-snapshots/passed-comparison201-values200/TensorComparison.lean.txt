/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct
public import Aglib.Algebra.Homology.TotalComplex.FirstQuadrant

/-!
# Whole comparison on the original total-degree fibers

The supplied homogeneous tensor laws and factorization identify the given
whole operator. The source equivalence and degree maps remain the supplied
ones, and every comparison is proved before a geometric specialization.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

universe u m n p v

namespace DirectSum

variable {R : Type u} [CommSemiring R]
  (M : ℕ → Type m) (N : ℕ → Type n)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ j, AddCommMonoid (N j)] [∀ j, Module R (N j)]

private theorem tensorPiLinearMap_eq_of_values
    (P : ℕ → Type p) [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    (E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ t, ⨁ s : HomologicalComplex₂.TotalDegree t,
        M s.val.1 ⊗[R] N s.val.2)
    (hE : E = tensorFiberEquiv (R := R) M N
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (F : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ i, P i)
    (G : ∀ t, (⨁ s : HomologicalComplex₂.TotalDegree t,
      M s.val.1 ⊗[R] N s.val.2) →ₗ[R] P t)
    (h : ∀ i j (x : M i) (y : N j),
      F (lof R ℕ M i x ⊗ₜ[R] lof R ℕ N j y) =
        lof R ℕ P (i + j)
          (G (i + j) (lof R (HomologicalComplex₂.TotalDegree (i + j))
            (fun s => M s.val.1 ⊗[R] N s.val.2)
            ⟨(i, j), rfl⟩ (x ⊗ₜ[R] y)))) :
    F = mapAfterEquiv E G := by
  subst E
  exact tensorTotalLinearMap_eq (R := R) M N P F G h

variable {M N}

/-- The two original whole equations fix their actual maps and parents.
The conclusion retains the given total operator without rebuilding it. -/
theorem tensorPiLinearMap_eq
    {P : ℕ → Type p} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    {S : Type v} [AddCommMonoid S] [Module R S]
    {Φ : S →ₗ[R] ⨁ i, P i}
    {s : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] S}
    {T : ∀ i j, M i ⊗[R] N j →ₗ[R] P (i + j)}
    (hF : ∀ i j,
      Φ ∘ₗ s ∘ₗ TensorProduct.map (lof R ℕ M i) (lof R ℕ N j) =
        lof R ℕ P (i + j) ∘ₗ T i j)
    {E : ((⨁ i, M i) ⊗[R] ⨁ j, N j) ≃ₗ[R]
      ⨁ t, ⨁ s : HomologicalComplex₂.TotalDegree t,
        M s.val.1 ⊗[R] N s.val.2}
    {G : ∀ t, (⨁ s : HomologicalComplex₂.TotalDegree t,
      M s.val.1 ⊗[R] N s.val.2) →ₗ[R] P t}
    {L : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ i, P i}
    (hL : MapFactorization L E G)
    (hE : E = tensorFiberEquiv (R := R) M N
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)))
    (hG : ∀ i j,
      G (i + j) ∘ₗ
          lof R (HomologicalComplex₂.TotalDegree (i + j))
            (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(i, j), rfl⟩ = T i j) :
    Φ ∘ₗ s = L := by
  have hWhole : Φ ∘ₗ s = mapAfterEquiv E G := by
    apply tensorPiLinearMap_eq_of_values M N P E hE (Φ ∘ₗ s) G
    intro i j x y
    have hValue := LinearMap.congr_fun (hF i j) (x ⊗ₜ[R] y)
    have hOriginal := LinearMap.congr_fun (hG i j) (x ⊗ₜ[R] y)
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul] at hValue hOriginal
    exact hValue.trans (congrArg (lof R ℕ P (i + j)) hOriginal.symm)
  apply LinearMap.ext
  intro z
  exact (LinearMap.congr_fun hWhole z).trans (hL z).symm

end DirectSum
