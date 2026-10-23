/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.CrossedProduct.Coefficients
public import Mathlib.Algebra.Central.Basic

/-!
# The center of the actual Galois crossed product

Commutation with the diagonal field kills all nonidentity coefficients.
Commutation with translations then forces the remaining coefficient into the
base field by the native finite-Galois fixed-field theorem.
-/

@[expose] public noncomputable section

namespace groupCohomology.CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [Fintype Gal(L/K)] [DecidableEq Gal(L/K)]
variable {c : Gal(L/K) × Gal(L/K) → Lˣ}
variable (hc : IsMulCocycle₂ c) (h₁ : c (1, 1) = 1)

/-- The coefficient field is embedded in the actual crossed-product algebra. -/
def diagonalEmbedding : L →ₐ[K] algebra hc h₁ :=
  (diagonalHom (K := K)).codRestrict (algebra hc h₁) fun a => by
    change diagonal a ∈ carrier c
    have h := term_mem_carrier c a 1
    simpa only [term, translation_one hc h₁, mul_one, diagonalHom_apply] using h

/-- The literal weighted translation, as an element of the crossed product. -/
def translationElement (g : L ≃ₐ[K] L) : algebra hc h₁ :=
  ⟨translation c g, by
    change translation c g ∈ carrier c
    have h := term_mem_carrier c 1 g
    simpa only [term, ← diagonalHom_apply, map_one, one_mul] using h⟩

/-- An element commuting with the embedded extension field is diagonal. -/
theorem eq_diagonal_of_commutes (x : algebra hc h₁)
    (hx : ∀ a : L, diagonalEmbedding hc h₁ a * x = x * diagonalEmbedding hc h₁ a) :
    x = diagonalEmbedding hc h₁ ((x : Matrix Gal(L/K) Gal(L/K) L) 1 1) := by
  apply (coefficientEquiv hc h₁).injective
  funext g
  change (x : Matrix Gal(L/K) Gal(L/K) L) 1 g = diagonal ((x : Matrix Gal(L/K) Gal(L/K) L) 1 1) 1 g
  by_cases hg : g = 1
  · subst g
    simp [diagonal]
  have hz : (x : Matrix Gal(L/K) Gal(L/K) L) 1 g = 0 := by
    by_contra hn
    have heq : g = 1 := by
      ext a
      have h := congrArg (fun y : algebra hc h₁ => (y : Matrix Gal(L/K) Gal(L/K) L) 1 g) (hx a)
      change (diagonal a * (x : Matrix Gal(L/K) Gal(L/K) L) : Matrix Gal(L/K) Gal(L/K) L) 1 g =
        ((x : Matrix Gal(L/K) Gal(L/K) L) * diagonal a : Matrix Gal(L/K) Gal(L/K) L) 1 g at h
      simp only [diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
        AlgEquiv.one_apply] at h
      apply mul_left_cancel₀ hn
      simpa only [AlgEquiv.one_apply, mul_comm] using h.symm
    exact hg heq
  simp [diagonal, hz, Ne.symm hg]

/-- The center of the actual crossed product is exactly the scalar field. -/
theorem isCentral [FiniteDimensional K L] [IsGalois K L] :
    Algebra.IsCentral K (algebra hc h₁) where
  out x hx := by
    have hcomm := Subalgebra.mem_center_iff.mp hx
    have hxdiag := eq_diagonal_of_commutes hc h₁ x fun a => hcomm (diagonalEmbedding hc h₁ a)
    let a : L := (x : Matrix Gal(L/K) Gal(L/K) L) 1 1
    have hfixed : ∀ g : L ≃ₐ[K] L, g a = a := by
      intro g
      have h := hcomm (translationElement hc h₁ g)
      rw [hxdiag] at h
      have he := congrArg (fun y : algebra hc h₁ => (y : Matrix Gal(L/K) Gal(L/K) L) 1 g) h
      change (translation c g * diagonal a : Matrix Gal(L/K) Gal(L/K) L) 1 g =
        (diagonal a * translation c g : Matrix Gal(L/K) Gal(L/K) L) 1 g at he
      simp only [diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, AlgEquiv.one_apply,
        translation_apply, one_mul, ite_true, map_one_fst_of_isMulCocycle₂ hc, h₁,
        Units.val_one, one_mul, mul_one] at he
      exact he
    obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed a).mpr hfixed
    refine ⟨k, ?_⟩
    rw [hxdiag]
    change algebraMap K (algebra hc h₁) k = diagonalEmbedding hc h₁ a
    rw [← hk]
    exact (diagonalEmbedding hc h₁).commutes k |>.symm

end groupCohomology.CrossedProduct
