/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Polynomial.Laurent.ProjectorCech

/-! # Finite defects for actual Laurent projector-image Cech maps

Both original parametrix defects factor through finite coefficient windows. The maps land
in the actual projector images, with their literal subtype inclusions. Bounds are supplied
by the proved Laurent cutoff theorem when constructing the cochain model.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Polynomial/Laurent/ProjectorFiniteDefects.lean`
from the supplied frozen Quillen snapshot.
SHA-256: `49123bd33bb1bd6a12f3509c3d4f9bb7178879b61480737ea0cbc4e9a53ee7ac`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Polynomial LaurentPolynomial
open scoped LaurentPolynomial Matrix
universe u v w z
namespace LaurentPolynomial.Projector
open LaurentPolynomial.Cutoff
variable {R : Type u} [CommRing R] {ι κ : Type v} [Fintype ι] [Fintype κ]

/-- The right finite-window inclusion into the actual localized projector image. -/
def rangeRightWindow (p : Matrix ι ι R[X]) (g : Matrix ι κ R[T;T⁻¹])
    (hpg : plusMatrix p * g = g) (N : ℕ) :
    (κ → Fin N → R) →ₗ[R] LinearMap.range (action (plusMatrix p)) :=
  ((action g).comp (positiveRemainder.comp (plusEmbedding.comp (windowEmbedding N)))).codRestrict
    (LinearMap.range (action (plusMatrix p))) (fun x => by
      refine ⟨action g (positiveRemainder (plusEmbedding (windowEmbedding N x))), ?_⟩
      exact LinearMap.congr_fun ((action_mul _ _).trans (congrArg action hpg)) _)

/-- The actual finite coefficients of the inverse-transition negative remainder. -/
def rangeRightCoefficients (p : Matrix ι ι R[X]) (h : Matrix κ ι R[T;T⁻¹]) (N : ℕ)
    (hN : ∀ b : ι → R[X], ∀ i, matrixNegativeTrunc h b i ∈ Polynomial.degreeLT R N) :
    LinearMap.range (action (plusMatrix p)) →ₗ[R] (κ → Fin N → R) :=
  (matrixWindowCoefficients h N hN).comp
    ((minusCutoff.comp negativeRemainder).comp
      (LinearMap.range (action (plusMatrix p))).subtype)

/-- The original restricted differential and right finite defect satisfy the parametrix
identity. -/
theorem range_right_identity (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (g : Matrix ι κ R[T;T⁻¹]) (h : Matrix κ ι R[T;T⁻¹])
    (hp : p * p = p) (hpg : plusMatrix p * g = g)
    (hgh : g * h = plusMatrix p) (hgq : g * minusMatrix q = g)
    (N : ℕ)
    (hN : ∀ b : ι → R[X], ∀ i, matrixNegativeTrunc h b i ∈ Polynomial.degreeLT R N) :
    (rangeDifference p q g hp hpg).comp (rangeParametrix p q h) +
      (rangeRightWindow p g hpg N).comp (rangeRightCoefficients p h N hN) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change difference g (parametrix p q h x.val) +
    action g (positiveRemainder (plusEmbedding (windowEmbedding N
      (matrixWindowCoefficients h N hN (minusCutoff (negativeRemainder x.val)))))) = x.val
  have hw (b : ι → R[X]) : windowEmbedding N (matrixWindowCoefficients h N hN b) =
      matrixNegativeTrunc h b := by
    funext i
    exact matrix_window_factorization h N hN b i
  have hc (b : ι → R[X]) : plusCutoff (action h (minusEmbedding b)) =
      matrixNegativeTrunc h b := by
    funext i
    simp [plusCutoff, action, minusEmbedding, matrixNegativeTrunc,
      negativeTruncMul, Matrix.mulVec, dotProduct, map_sum]
  rw [hw, ← hc, minusEmbedding_minusCutoff_negativeRemainder,
    positiveRemainder_plusEmbedding_plusCutoff]
  exact right_defect p q g h hgh hgq x.val (laurentRange_fixed p hp x)

/-- The left finite-window map into the two actual polynomial projector images. -/
def rangeLeftWindow (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (h : Matrix κ ι R[T;T⁻¹]) (N : ℕ) :
    (ι → Fin N → R) →ₗ[R]
      (LinearMap.range (polynomialAction p) × LinearMap.range (polynomialAction q)) :=
  (((polynomialAction p).rangeRestrict).prod
    ((polynomialAction q).rangeRestrict.comp
      (minusCutoff.comp ((action h).comp plusEmbedding)))).comp (windowEmbedding N)

/-- The original finite coefficients of the transition on the negative chart input. -/
def rangeLeftCoefficients (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (g : Matrix ι κ R[T;T⁻¹]) (N : ℕ)
    (hN : ∀ b : κ → R[X], ∀ i, matrixNegativeTrunc g b i ∈ Polynomial.degreeLT R N) :
    (LinearMap.range (polynomialAction p) × LinearMap.range (polynomialAction q)) →ₗ[R]
      (ι → Fin N → R) :=
  (matrixWindowCoefficients g N hN).comp
    ((LinearMap.range (polynomialAction q)).subtype.comp (LinearMap.snd R _ _))

/-- The original restricted parametrix and left finite defect satisfy the identity. -/
theorem range_left_identity (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (g : Matrix ι κ R[T;T⁻¹]) (h : Matrix κ ι R[T;T⁻¹])
    (hp : p * p = p) (hq : q * q = q) (hpg : plusMatrix p * g = g)
    (hhg : h * g = minusMatrix q) (N : ℕ)
    (hN : ∀ b : κ → R[X], ∀ i, matrixNegativeTrunc g b i ∈ Polynomial.degreeLT R N) :
    (rangeParametrix p q h).comp (rangeDifference p q g hp hpg) +
      (rangeLeftWindow p q h N).comp (rangeLeftCoefficients p q g N hN) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hw : windowEmbedding N (matrixWindowCoefficients g N hN x.2.val) =
      matrixNegativeTrunc g x.2.val := by
    funext i
    exact matrix_window_factorization g N hN x.2.val i
  have he := left_defect p q g h hhg x.1.val x.2.val
    (polynomialRange_fixed p hp x.1) (polynomialRange_fixed q hq x.2)
  apply Prod.ext
  · apply Subtype.ext
    change (parametrix p q h (difference g (x.1.val,x.2.val))).1 +
      polynomialAction p (windowEmbedding N (matrixWindowCoefficients g N hN x.2.val)) = x.1.val
    rw [hw]
    exact congrArg Prod.fst he
  · apply Subtype.ext
    change (parametrix p q h (difference g (x.1.val,x.2.val))).2 +
      polynomialAction q (minusCutoff (action h (plusEmbedding
        (windowEmbedding N (matrixWindowCoefficients g N hN x.2.val))))) = x.2.val
    rw [hw]
    exact congrArg Prod.snd he

end LaurentPolynomial.Projector
