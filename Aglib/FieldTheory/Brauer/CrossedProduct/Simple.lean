/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.CrossedProduct.Center
public import Aglib.FieldTheory.Separable.TensorProductSplitting
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Simplicity of the matrix crossed product

Simultaneous evaluation of the separable tensor product isolates any chosen
coefficient by a sum of left and right diagonal multiplications. A nonzero
ideal therefore contains a nonzero single translation term, which is a unit.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace groupCohomology.CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [Fintype Gal(L/K)] [DecidableEq Gal(L/K)]
variable {c : Gal(L/K) × Gal(L/K) → Lˣ}
variable (hc : IsMulCocycle₂ c) (h₁ : c (1, 1) = 1)

/-- Each translation is a unit in the actual subalgebra, not merely in the ambient matrix ring. -/
theorem isUnit_translation (g : L ≃ₐ[K] L) : IsUnit (translationElement hc h₁ g) := by
  apply isUnit_of_mul_isUnit_left (y := translationElement hc h₁ g⁻¹)
  have he : translationElement hc h₁ g * translationElement hc h₁ g⁻¹ =
      diagonalEmbedding hc h₁ (c (g, g⁻¹) : L) := by
    apply Subtype.ext
    change translation c g * translation c g⁻¹ = diagonal (c (g, g⁻¹) : L)
    rw [translation_mul_translation hc, mul_inv_cancel, translation_one hc h₁, mul_one]
  rw [he]
  exact (c (g, g⁻¹)).isUnit.map (diagonalEmbedding hc h₁)

/-- The bilinear action of two diagonal coefficients on an algebra element. -/
def sandwich (x : algebra hc h₁) : L ⊗[K] L →ₗ[K] algebra hc h₁ :=
  TensorProduct.lift (LinearMap.mk₂ K
    (fun a b => diagonalEmbedding hc h₁ a * x * diagonalEmbedding hc h₁ b)
    (by intros; simp only [map_add, add_mul])
    (by intros; simp only [map_smul, smul_mul_assoc])
    (by intros; simp only [map_add, mul_add])
    (by intros; simp only [map_smul, mul_smul_comm]))

@[simp]
theorem sandwich_tmul (x : algebra hc h₁) (a b : L) :
    sandwich hc h₁ x (a ⊗ₜ[K] b) =
      diagonalEmbedding hc h₁ a * x * diagonalEmbedding hc h₁ b := rfl

/-- Sandwiching preserves every two-sided ideal. -/
theorem sandwich_mem (I : TwoSidedIdeal (algebra hc h₁))
    {x : algebra hc h₁} (hx : x ∈ I) (t : L ⊗[K] L) : sandwich hc h₁ x t ∈ I := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hx)
  | add t u ht hu =>
    simpa only [map_add] using I.add_mem ht hu

/-- The sandwich tensor acts coefficientwise by simultaneous Galois evaluation. -/
theorem sandwich_coefficient (x : algebra hc h₁) (t : L ⊗[K] L) (g : L ≃ₐ[K] L) :
    (sandwich hc h₁ x t : Matrix Gal(L/K) Gal(L/K) L) 1 g =
      Algebra.IsSeparable.tensorProductEvaluation K L L t g.toAlgHom *
        (x : Matrix Gal(L/K) Gal(L/K) L) 1 g := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    change (diagonal a * (x : Matrix Gal(L/K) Gal(L/K) L) * diagonal b :
        Matrix Gal(L/K) Gal(L/K) L) 1 g =
      (a * g b) * (x : Matrix Gal(L/K) Gal(L/K) L) 1 g
    simp only [diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, AlgEquiv.one_apply]
    ring
  | add t u ht hu =>
    simp only [map_add, Pi.add_apply, Subalgebra.coe_add, Matrix.add_apply, ht, hu, add_mul]

/-- Every nonzero coefficient of an ideal element yields a unit in that ideal. -/
theorem ideal_contains_single_term [FiniteDimensional K L]
    (I : TwoSidedIdeal (algebra hc h₁)) {x : algebra hc h₁} (hx : x ∈ I)
    (g : L ≃ₐ[K] L) :
    diagonalEmbedding hc h₁ ((x : Matrix Gal(L/K) Gal(L/K) L) 1 g) *
      translationElement hc h₁ g ∈ I := by
  classical
  obtain ⟨t, ht⟩ := Algebra.IsSeparable.tensorProductEvaluation_surjective K L L
    (fun σ => if σ = g.toAlgHom then 1 else 0)
  have he : sandwich hc h₁ x t =
      diagonalEmbedding hc h₁ ((x : Matrix Gal(L/K) Gal(L/K) L) 1 g) *
        translationElement hc h₁ g := by
    apply (coefficientEquiv hc h₁).injective
    funext h
    change (sandwich hc h₁ x t : Matrix Gal(L/K) Gal(L/K) L) 1 h =
      term c ((x : Matrix Gal(L/K) Gal(L/K) L) 1 g) g 1 h
    rw [sandwich_coefficient, term_one_apply hc h₁]
    have hh := congrFun ht h.toAlgHom
    rw [hh]
    by_cases hgh : h = g
    · subst h
      simp
    · have hne : h.toAlgHom ≠ g.toAlgHom := fun he => hgh (AlgEquiv.coe_toAlgHom_injective he)
      simp [hne, Ne.symm hgh]
  rw [← he]
  exact sandwich_mem hc h₁ I hx t

/-- The literal matrix crossed product is a simple ring. -/
theorem isSimpleRing [FiniteDimensional K L] : IsSimpleRing (algebra hc h₁) := by
  classical
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  obtain ⟨x, hxI, hx : x ≠ 0⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
  obtain ⟨g, hg⟩ : ∃ g : L ≃ₐ[K] L, (x : Matrix Gal(L/K) Gal(L/K) L) 1 g ≠ 0 := by
    by_contra h
    apply hx
    apply (coefficientEquiv hc h₁).injective
    ext g
    have hz : ∀ g : L ≃ₐ[K] L, (x : Matrix Gal(L/K) Gal(L/K) L) 1 g = 0 := by
      simpa only [not_exists, not_not] using h
    exact hz g
  have hu : IsUnit (diagonalEmbedding hc h₁ ((x : Matrix Gal(L/K) Gal(L/K) L) 1 g) *
      translationElement hc h₁ g) :=
    ((isUnit_iff_ne_zero.mpr hg).map (diagonalEmbedding hc h₁)).mul
      (isUnit_translation hc h₁ g)
  obtain ⟨u, hu⟩ := hu
  have hm := ideal_contains_single_term hc h₁ I hxI g
  rw [← hu] at hm
  apply I.eq_top
  simpa only [Units.inv_mul] using I.mul_mem_left (↑u⁻¹) _ hm

end groupCohomology.CrossedProduct
