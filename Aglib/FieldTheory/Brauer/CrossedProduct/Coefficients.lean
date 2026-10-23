/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.CrossedProduct.Algebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Coefficients in the matrix crossed product

The first row of a normalized crossed-product matrix is its coefficient vector.
The explicit linear equivalence with a product of copies of the extension field
proves the expected dimension without treating a basis as an assumption.
-/

@[expose] public noncomputable section

namespace groupCohomology.CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [Fintype (L ≃ₐ[K] L)] [DecidableEq (L ≃ₐ[K] L)]
variable {c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}

/-- Each generating matrix has exactly one nonzero coefficient in its first row. -/
theorem term_one_apply (hc : IsMulCocycle₂ c) (h₁ : c (1, 1) = 1)
    (a : L) (g h : L ≃ₐ[K] L) :
    term c a g 1 h = if g = h then a else 0 := by
  rw [term, diagonal_mul_apply, translation_apply]
  simp only [AlgEquiv.one_apply, one_mul, map_one_fst_of_isMulCocycle₂ hc, h₁,
    Units.val_one, mul_ite, mul_one, mul_zero]

/-- Form a matrix from its explicit coefficient vector. -/
def fromCoefficients (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) :
    ((L ≃ₐ[K] L) → L) →ₗ[K] Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L where
  toFun a := ∑ g, term c (a g) g
  map_add' a b := by
    simp only [Pi.add_apply, term, ← diagonalHom_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, term, ← diagonalHom_apply, map_smul, smul_mul_assoc,
      Finset.smul_sum, RingHom.id_apply]

@[simp]
theorem fromCoefficients_apply (a : (L ≃ₐ[K] L) → L) :
    fromCoefficients c a = ∑ g, term c (a g) g := rfl

/-- Reading the first row recovers the original vector. -/
theorem fromCoefficients_one_apply (hc : IsMulCocycle₂ c) (h₁ : c (1, 1) = 1)
    (a : (L ≃ₐ[K] L) → L) (g : L ≃ₐ[K] L) :
    fromCoefficients c a 1 g = a g := by
  simp only [fromCoefficients_apply, Matrix.sum_apply, term_one_apply hc h₁]
  simp

/-- Reconstruction fixes every element of the literal spanning submodule. -/
theorem fromCoefficients_row (hc : IsMulCocycle₂ c) (h₁ : c (1, 1) = 1)
    {x : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L} (hx : x ∈ carrier c) :
    fromCoefficients c (fun g => x 1 g) = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, g⟩, rfl⟩ := hx
    simp only [fromCoefficients_apply, term_one_apply hc h₁]
    have hz (h : L ≃ₐ[K] L) : term c 0 h = 0 := by
      simp only [term, ← diagonalHom_apply, map_zero, zero_mul]
    have ht (h : L ≃ₐ[K] L) :
        term c (if g = h then a else 0) h = if g = h then term c a g else 0 := by
      split_ifs with hgh
      · subst h
        rfl
      · exact hz h
    simp_rw [ht]
    simp
  | zero =>
    change fromCoefficients c 0 = 0
    exact map_zero _
  | add x y hx hy ihx ihy =>
    change fromCoefficients c ((fun g => x 1 g) + fun g => y 1 g) = x + y
    rw [map_add, ihx, ihy]
  | smul r x hx ih =>
    change fromCoefficients c (r • fun g => x 1 g) = r • x
    rw [map_smul, ih]

/-- Every explicit coefficient vector gives an element of the crossed product. -/
theorem fromCoefficients_mem (a : (L ≃ₐ[K] L) → L) :
    fromCoefficients c a ∈ carrier c :=
  Submodule.sum_mem _ fun g _ => term_mem_carrier c (a g) g

/-- The coefficient-vector linear equivalence for the actual crossed-product algebra. -/
def coefficientEquiv (hc : IsMulCocycle₂ c) (h₁ : c (1, 1) = 1) :
    algebra hc h₁ ≃ₗ[K] ((L ≃ₐ[K] L) → L) where
  toFun x g := (x : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) 1 g
  invFun a := ⟨fromCoefficients c a, fromCoefficients_mem a⟩
  left_inv x := by
    apply Subtype.ext
    change fromCoefficients c (fun g => (x : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) 1 g) =
      (x : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L)
    apply fromCoefficients_row hc h₁
    exact x.property
  right_inv a := by
    funext g
    change fromCoefficients c a 1 g = a g
    exact fromCoefficients_one_apply hc h₁ a g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The dimension follows from the constructed coefficient equivalence. -/
theorem finrank_algebra [FiniteDimensional K L]
    (hc : IsMulCocycle₂ c) (h₁ : c (1, 1) = 1) :
    Module.finrank K (algebra hc h₁) = Fintype.card (L ≃ₐ[K] L) * Module.finrank K L := by
  rw [(coefficientEquiv hc h₁).finrank_eq, Module.finrank_pi_fintype]
  simp

end groupCohomology.CrossedProduct
