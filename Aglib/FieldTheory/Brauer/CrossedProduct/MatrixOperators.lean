/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Matrix operators attached to a Galois two-cocycle

These are literal matrices over the extension field. Their multiplication is
native matrix multiplication; the cocycle identity proves the crossed-product
relations rather than being used to postulate a ring structure.
-/

@[expose] public noncomputable section

namespace groupCohomology
namespace CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [DecidableEq (L ≃ₐ[K] L)]

/-- The diagonal embedding recording all Galois conjugates. -/
def diagonal (a : L) : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L :=
  Matrix.diagonal fun σ => σ a

/-- A weighted right-translation matrix for a multiplicative two-cochain. -/
def translation (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (g : L ≃ₐ[K] L) :
    Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := by
  classical
  exact fun σ τ => if σ * g = τ then (c (σ, g) : L) else 0

@[simp]
theorem translation_apply (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (g σ τ : L ≃ₐ[K] L) :
    translation c g σ τ = if σ * g = τ then (c (σ, g) : L) else 0 := by
  classical
  rfl

variable [Fintype (L ≃ₐ[K] L)]

/-- Multiplication by the diagonal embedding is rowwise multiplication. -/
theorem diagonal_mul_apply (a : L) (M : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L)
    (σ τ : L ≃ₐ[K] L) : (diagonal a * M : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) σ τ = σ a * M σ τ := by
  classical
  exact Matrix.diagonal_mul _ _ _ _

/-- Right multiplication by the diagonal embedding twists coefficients. -/
theorem translation_mul_diagonal
    (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (g : L ≃ₐ[K] L) (a : L) :
    translation c g * diagonal a = diagonal (g a) * translation c g := by
  classical
  ext σ τ
  simp only [diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, translation_apply]
  split_ifs with h
  · subst τ
    simp [AlgEquiv.mul_apply, mul_comm]
  · simp

/-- The native multiplicative cocycle equation gives the twisted product law. -/
theorem translation_mul_translation
    {c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hc : IsMulCocycle₂ c)
    (g h : L ≃ₐ[K] L) :
    translation c g * translation c h = diagonal (c (g, h) : L) * translation c (g * h) := by
  classical
  ext σ τ
  rw [Matrix.mul_apply, diagonal_mul_apply]
  rw [Finset.sum_eq_single (σ * g)]
  · rw [translation_apply, ite_eq_left rfl, translation_apply, translation_apply, mul_assoc]
    split_ifs with he
    · have hh := congrArg (fun u : Lˣ => (u : L)) (hc σ g h)
      change (c (σ * g, h) : L) * (c (σ, g) : L) =
        σ (c (g, h) : L) * (c (σ, g * h) : L) at hh
      simpa only [mul_comm] using hh
    · simp
  · intro b hb hbne
    simp [translation_apply, Ne.symm hbne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

omit [Fintype (L ≃ₐ[K] L)] in
/-- Normalization at the identity makes the identity translation the unit matrix. -/
theorem translation_one
    {c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hc : IsMulCocycle₂ c)
    (h₁ : c (1, 1) = 1) : translation c 1 = 1 := by
  classical
  ext σ τ
  simp only [translation_apply, mul_one, Matrix.one_apply]
  rw [map_one_snd_of_isMulCocycle₂ hc, h₁, smul_one, Units.val_one]

end CrossedProduct
end groupCohomology
