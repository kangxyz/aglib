/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct.PointNaturality

/-! # Point diagrams at the original total maps -/

@[expose] public noncomputable section

open scoped TensorProduct

universe u m n p

namespace DirectSum

variable {R : Type u} [Field R]
  {M : ℕ → Type m} {N : ℕ → Type n} {P : ℕ → Type p}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  {cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d}

/-- Retain the given original total maps in the left point diagram. -/
theorem tensorPointLeftDiagramWithTotals {v : ∀ d, P d →ₗ[R] N d}
    {e : DirectSum ℕ M →ₗ[R] R} (h : tensorPointLeftDiagram M N P cup v e)
    (L : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R] DirectSum ℕ P)
    (point : DirectSum ℕ P →ₗ[R] DirectSum ℕ N)
    (hL : L = canonicalTotalCupMap M N P cup) (hp : point = lmap v) :
    point ∘ₗ L =
      (TensorProduct.lid R (DirectSum ℕ N)).toLinearMap ∘ₗ e.rTensor (DirectSum ℕ N) := by
  rw [hL, hp]
  exact h

/-- Retain the given original total maps in the right point diagram. -/
theorem tensorPointRightDiagramWithTotals {v : ∀ d, P d →ₗ[R] M d}
    {e : DirectSum ℕ N →ₗ[R] R} (h : tensorPointRightDiagram M N P cup v e)
    (L : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R] DirectSum ℕ P)
    (point : DirectSum ℕ P →ₗ[R] DirectSum ℕ M)
    (hL : L = canonicalTotalCupMap M N P cup) (hp : point = lmap v) :
    point ∘ₗ L =
      (TensorProduct.rid R (DirectSum ℕ M)).toLinearMap ∘ₗ e.lTensor (DirectSum ℕ M) := by
  rw [hL, hp]
  exact h

end DirectSum
