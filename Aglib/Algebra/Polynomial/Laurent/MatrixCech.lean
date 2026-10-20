/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Polynomial.Laurent.MatrixCutoff
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.Abel

/-! # Original Laurent-matrix Cech parametrices and both finite defects

For specified inverse Laurent transition matrices, the literal signed map is
positive restriction minus the transition times negative restriction. Its actual cutoff
parametrix has both original defect identities. Each defect factors through an actual
finite coefficient module using the uniform bounds proved for Laurent matrices.
This is a coordinate calculation for finite free chart modules, not a theorem that
arbitrary vector bundles admit free chart trivializations.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Polynomial/Laurent/MatrixCech.lean` from the
supplied frozen Quillen snapshot.
SHA-256: `3c517cbf1a29ec130b4b334b228e5463b4bce6c5e2f4c3d62e523bca08b5ccd1`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
open Polynomial LaurentPolynomial
open scoped LaurentPolynomial Matrix
universe u v
namespace LaurentPolynomial.Cutoff
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]

/-- Original coordinatewise positive-chart restriction. -/
def plusEmbedding : (ι → R[X]) →ₗ[R] (ι → R[T;T⁻¹]) :=
  LinearMap.piMap fun _ => Polynomial.toLaurentAlg.toLinearMap

/-- Original coordinatewise negative-chart restriction. -/
def minusEmbedding : (ι → R[X]) →ₗ[R] (ι → R[T;T⁻¹]) :=
  LinearMap.piMap fun _ =>
    LaurentPolynomial.invert.toLinearMap.comp Polynomial.toLaurentAlg.toLinearMap

/-- Original coordinatewise nonnegative truncation. -/
def plusCutoff : (ι → R[T;T⁻¹]) →ₗ[R] (ι → R[X]) :=
  LinearMap.piMap fun _ => truncLinear R

/-- Original coordinatewise nonpositive truncation expressed in the negative coordinate. -/
def minusCutoff : (ι → R[T;T⁻¹]) →ₗ[R] (ι → R[X]) :=
  LinearMap.piMap fun _ => (truncLinear R).comp LaurentPolynomial.invert.toLinearMap

/-- Strictly negative original coordinate remainder. -/
def negativeRemainder : (ι → R[T;T⁻¹]) →ₗ[R] (ι → R[T;T⁻¹]) :=
  LinearMap.id - plusEmbedding.comp plusCutoff

/-- Strictly positive original coordinate remainder. -/
def positiveRemainder : (ι → R[T;T⁻¹]) →ₗ[R] (ι → R[T;T⁻¹]) :=
  LinearMap.id - minusEmbedding.comp minusCutoff

/-- Multiplication by the actual Laurent transition matrix with its original coefficient action. -/
def matrixAction (g : Matrix ι ι R[T;T⁻¹]) :
    (ι → R[T;T⁻¹]) →ₗ[R] (ι → R[T;T⁻¹]) :=
  g.mulVecLin.restrictScalars R

/-- The original signed two-chart differential in specified free chart coordinates. -/
def matrixDifference (g : Matrix ι ι R[T;T⁻¹]) :
    (ι → R[X]) × (ι → R[X]) →ₗ[R] (ι → R[T;T⁻¹]) :=
  plusEmbedding.comp (LinearMap.fst R _ _) -
    (matrixAction g).comp (minusEmbedding.comp (LinearMap.snd R _ _))

/-- The actual cutoff parametrix uses the specified inverse transition matrix. -/
def matrixParametrix (h : Matrix ι ι R[T;T⁻¹]) :
    (ι → R[T;T⁻¹]) →ₗ[R] ((ι → R[X]) × (ι → R[X])) :=
  plusCutoff.prod (-(minusCutoff.comp ((matrixAction h).comp negativeRemainder)))

omit [Fintype ι] in
/-- The original positive chart restriction is split by the original truncation. -/
theorem plusCutoff_plusEmbedding (a : ι → R[X]) :
    plusCutoff (plusEmbedding a) = a := by
  funext i
  exact Polynomial.trunc_toLaurent (a i)

omit [Fintype ι] in
/-- The negative chart restriction is split using the actual involution. -/
theorem minusCutoff_minusEmbedding (b : ι → R[X]) :
    minusCutoff (minusEmbedding b) = b := by
  funext i
  change trunc (invert (invert (toLaurent (b i)))) = b i
  rw [involutive_invert, Polynomial.trunc_toLaurent]

/-- The actual matrix multiplication identities remain the original linear-map identities. -/
theorem matrixAction_comp [DecidableEq ι] (g h : Matrix ι ι R[T;T⁻¹])
    (hgh : g * h = 1) : (matrixAction g).comp (matrixAction h) = LinearMap.id := by
  apply LinearMap.ext
  intro b
  funext i
  change (g *ᵥ (h *ᵥ b)) i = b i
  rw [Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec]

/-- Cutoff after the actual negative-chart matrix map is the previously bounded literal map. -/
theorem plusCutoff_matrixAction_minusEmbedding (g : Matrix ι ι R[T;T⁻¹]) (b : ι → R[X]) :
    plusCutoff (matrixAction g (minusEmbedding b)) = matrixNegativeTrunc g b := by
  funext i
  simp [plusCutoff, matrixAction, minusEmbedding, matrixNegativeTrunc,
    negativeTruncMul, Matrix.mulVec, dotProduct, map_sum]

end LaurentPolynomial.Cutoff

namespace LaurentPolynomial.Cutoff
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The actual right defect uses the strictly positive cutoff of the inverse transition. -/
def matrixRightDefect (g h : Matrix ι ι R[T;T⁻¹]) :
    (ι → R[T;T⁻¹]) →ₗ[R] (ι → R[T;T⁻¹]) :=
  (matrixAction g).comp (positiveRemainder.comp ((matrixAction h).comp negativeRemainder))

/-- The left defect's original two chart columns are determined by its positive output. -/
def matrixLeftColumns (h : Matrix ι ι R[T;T⁻¹]) :
    (ι → R[X]) →ₗ[R] ((ι → R[X]) × (ι → R[X])) :=
  LinearMap.id.prod (minusCutoff.comp ((matrixAction h).comp plusEmbedding))

omit [Fintype ι] [DecidableEq ι] in
/-- The original negative remainder vanishes on positive chart inputs. -/
theorem negativeRemainder_plusEmbedding (a : ι → R[X]) :
    negativeRemainder (plusEmbedding a) = 0 := by
  change plusEmbedding a - plusEmbedding (plusCutoff (plusEmbedding a)) = 0
  rw [plusCutoff_plusEmbedding, sub_self]

/-- The actual inverse-matrix relation identifies the right parametrix defect exactly. -/
theorem matrix_right_defect (g h : Matrix ι ι R[T;T⁻¹]) (hgh : g * h = 1) :
    (matrixDifference g).comp (matrixParametrix h) + matrixRightDefect g h = LinearMap.id := by
  apply LinearMap.ext
  intro w
  change plusEmbedding (plusCutoff w) -
      matrixAction g (minusEmbedding (-minusCutoff (matrixAction h (negativeRemainder w)))) +
      matrixAction g (matrixAction h (negativeRemainder w) -
        minusEmbedding (minusCutoff (matrixAction h (negativeRemainder w)))) = w
  simp only [map_neg, map_sub]
  rw [show matrixAction g (matrixAction h (negativeRemainder w)) = negativeRemainder w from
    LinearMap.congr_fun (matrixAction_comp g h hgh) _]
  change plusEmbedding (plusCutoff w) -
      -matrixAction g (minusEmbedding (minusCutoff (matrixAction h (negativeRemainder w)))) +
      (w - plusEmbedding (plusCutoff w) -
        matrixAction g (minusEmbedding (minusCutoff (matrixAction h (negativeRemainder w))))) = w
  abel

/-- The left defect factors through the actual positive part
of the transition on the second chart. -/
theorem matrix_left_defect (g h : Matrix ι ι R[T;T⁻¹]) (hhg : h * g = 1) :
    (matrixParametrix h).comp (matrixDifference g) +
      (matrixLeftColumns h).comp ((matrixNegativeTrunc g).comp (LinearMap.snd R _ _)) =
        LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨a,b⟩
  apply Prod.ext
  · change plusCutoff (plusEmbedding a - matrixAction g (minusEmbedding b)) +
        matrixNegativeTrunc g b = a
    rw [map_sub, plusCutoff_plusEmbedding, plusCutoff_matrixAction_minusEmbedding]
    abel
  · change -minusCutoff (matrixAction h
        (negativeRemainder (plusEmbedding a - matrixAction g (minusEmbedding b)))) +
        minusCutoff (matrixAction h (plusEmbedding (matrixNegativeTrunc g b))) = b
    rw [map_sub, negativeRemainder_plusEmbedding, zero_sub, map_neg, map_neg, neg_neg]
    rw [← map_add, ← map_add, ← plusCutoff_matrixAction_minusEmbedding]
    have he : negativeRemainder (matrixAction g (minusEmbedding b)) +
        plusEmbedding (plusCutoff (matrixAction g (minusEmbedding b))) =
          matrixAction g (minusEmbedding b) := sub_add_cancel _ _
    rw [he]
    rw [show matrixAction h (matrixAction g (minusEmbedding b)) = minusEmbedding b from
      LinearMap.congr_fun (matrixAction_comp h g hhg) _]
    exact minusCutoff_minusEmbedding b

end LaurentPolynomial.Cutoff

namespace LaurentPolynomial.Cutoff
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]

/-- The coordinatewise original finite-window polynomial inclusion. -/
def windowEmbedding (N : ℕ) : (ι → Fin N → R) →ₗ[R] (ι → R[X]) :=
  LinearMap.piMap fun _ => windowInclusion N

/-- The original finite coefficient vectors reconstruct the actual matrix cutoff. -/
theorem windowEmbedding_matrixWindowCoefficients
    (g : Matrix ι ι R[T;T⁻¹]) (N : ℕ)
    (hN : ∀ b : ι → R[X], ∀ i, matrixNegativeTrunc g b i ∈ Polynomial.degreeLT R N)
    (b : ι → R[X]) :
    windowEmbedding N (matrixWindowCoefficients g N hN b) = matrixNegativeTrunc g b := by
  funext i
  exact matrix_window_factorization g N hN b i

omit [Fintype ι] in
/-- The negative remainder is recovered in the actual negative-chart coordinate. -/
theorem minusEmbedding_minusCutoff_negativeRemainder (w : ι → R[T;T⁻¹]) :
    minusEmbedding (minusCutoff (negativeRemainder w)) = negativeRemainder w := by
  funext i
  exact nonpositive_negative (w i)

omit [Fintype ι] in
/-- The strictly positive remainder depends only on the original nonnegative cutoff. -/
theorem positiveRemainder_plusEmbedding_plusCutoff (w : ι → R[T;T⁻¹]) :
    positiveRemainder (plusEmbedding (plusCutoff w)) = positiveRemainder w := by
  funext i
  exact positive_nonnegative (w i)

/-- The actual right-defect inclusion retains the positive cutoff and transition matrix. -/
def rightWindowInclusion (g : Matrix ι ι R[T;T⁻¹]) (N : ℕ) :
    (ι → Fin N → R) →ₗ[R] (ι → R[T;T⁻¹]) :=
  (matrixAction g).comp (positiveRemainder.comp (plusEmbedding.comp (windowEmbedding N)))

/-- The actual inverse-transition window coefficients of the original negative remainder. -/
def rightWindowCoefficients (h : Matrix ι ι R[T;T⁻¹]) (N : ℕ)
    (hN : ∀ b : ι → R[X], ∀ i, matrixNegativeTrunc h b i ∈ Polynomial.degreeLT R N) :
    (ι → R[T;T⁻¹]) →ₗ[R] (ι → Fin N → R) :=
  (matrixWindowCoefficients h N hN).comp (minusCutoff.comp negativeRemainder)

/-- The right defect factors through the actual finite coefficient module, with unchanged maps. -/
theorem right_window_defect_factorization (g h : Matrix ι ι R[T;T⁻¹]) (N : ℕ)
    (hN : ∀ b : ι → R[X], ∀ i, matrixNegativeTrunc h b i ∈ Polynomial.degreeLT R N) :
    (rightWindowInclusion g N).comp (rightWindowCoefficients h N hN) = matrixRightDefect g h := by
  apply LinearMap.ext
  intro w
  change matrixAction g (positiveRemainder (plusEmbedding (windowEmbedding N
    (matrixWindowCoefficients h N hN (minusCutoff (negativeRemainder w)))))) =
      matrixAction g (positiveRemainder (matrixAction h (negativeRemainder w)))
  rw [windowEmbedding_matrixWindowCoefficients, ← plusCutoff_matrixAction_minusEmbedding,
    minusEmbedding_minusCutoff_negativeRemainder, positiveRemainder_plusEmbedding_plusCutoff]

/-- The left defect factors through the actual finite coefficient module of the transition. -/
theorem left_window_defect_factorization (g h : Matrix ι ι R[T;T⁻¹]) (N : ℕ)
    (hN : ∀ b : ι → R[X], ∀ i, matrixNegativeTrunc g b i ∈ Polynomial.degreeLT R N) :
    ((matrixLeftColumns h).comp (windowEmbedding N)).comp
        ((matrixWindowCoefficients g N hN).comp (LinearMap.snd R (ι → R[X]) (ι → R[X]))) =
      (matrixLeftColumns h).comp
        ((matrixNegativeTrunc g).comp (LinearMap.snd R (ι → R[X]) (ι → R[X]))) := by
  apply LinearMap.ext
  rintro ⟨a,b⟩
  change matrixLeftColumns h (windowEmbedding N (matrixWindowCoefficients g N hN b)) =
    matrixLeftColumns h (matrixNegativeTrunc g b)
  rw [windowEmbedding_matrixWindowCoefficients]

end LaurentPolynomial.Cutoff
