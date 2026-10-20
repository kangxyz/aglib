/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Polynomial.Laurent.MatrixProjector

/-! # Signed Cech maps on actual polynomial projector images

The literal difference a - G b and its projected cutoff parametrix are restricted to
the genuine image modules. Both defect identities retain the explicit Laurent transition
and projector equations; rectangular chart ranks may differ.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Polynomial/Laurent/ProjectorCech.lean` from the
supplied frozen Quillen snapshot.
SHA-256: `fe094d8b4e3a50d7d441dde8704fcc2e4a312278d494b3277a2011828d81f9d3`.
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
variable {R : Type u} [CommRing R]
variable {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

/-- The literal positive-minus-transition-times-negative differential for rectangular
matrices. -/
def difference (g : Matrix ι κ R[T;T⁻¹]) :
    ((ι → R[X]) × (κ → R[X])) →ₗ[R] (ι → R[T;T⁻¹]) :=
  plusEmbedding.comp (LinearMap.fst R _ _) -
    (action g).comp (minusEmbedding.comp (LinearMap.snd R _ _))

/-- The original cutoffs sandwiched by the two polynomial chart projectors. -/
def parametrix (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (h : Matrix κ ι R[T;T⁻¹]) :
    (ι → R[T;T⁻¹]) →ₗ[R] ((ι → R[X]) × (κ → R[X])) :=
  ((polynomialAction p).comp plusCutoff).prod
    (- (polynomialAction q).comp (minusCutoff.comp ((action h).comp negativeRemainder)))

/-- The right defect on the actual fixed target is the original strictly positive Laurent
tail. -/
theorem right_defect (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (g : Matrix ι κ R[T;T⁻¹]) (h : Matrix κ ι R[T;T⁻¹])
    (hgh : g * h = plusMatrix p) (hgq : g * minusMatrix q = g)
    (w : ι → R[T;T⁻¹]) (hw : action (plusMatrix p) w = w) :
    difference g (parametrix p q h w) +
      action g (positiveRemainder (action h (negativeRemainder w))) = w := by
  change plusEmbedding (polynomialAction p (plusCutoff w)) -
      action g (minusEmbedding (-polynomialAction q
        (minusCutoff (action h (negativeRemainder w))))) +
      action g (action h (negativeRemainder w) -
        minusEmbedding (minusCutoff (action h (negativeRemainder w)))) = w
  rw [map_neg, plusEmbedding_polynomialAction, minusEmbedding_polynomialAction]
  simp only [map_neg, map_sub]
  have hq (x : κ → R[T;T⁻¹]) : action g (action (minusMatrix q) x) = action g x := by
    exact LinearMap.congr_fun ((action_mul g (minusMatrix q)).trans (congrArg action hgq)) x
  have he (x : ι → R[T;T⁻¹]) : action g (action h x) = action (plusMatrix p) x := by
    exact LinearMap.congr_fun ((action_mul g h).trans (congrArg action hgh)) x
  rw [hq, he]
  change action (plusMatrix p) (plusEmbedding (plusCutoff w)) - -_ +
      (action (plusMatrix p) (w - plusEmbedding (plusCutoff w)) - _) = w
  rw [map_sub, hw]
  abel

/-- The left defect on the actual fixed chart inputs factors through their positive transition
tail. -/
theorem left_defect (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (g : Matrix ι κ R[T;T⁻¹]) (h : Matrix κ ι R[T;T⁻¹])
    (hhg : h * g = minusMatrix q)
    (a : ι → R[X]) (b : κ → R[X])
    (ha : polynomialAction p a = a) (hb : polynomialAction q b = b) :
    parametrix p q h (difference g (a,b)) +
      (polynomialAction p (matrixNegativeTrunc g b),
        polynomialAction q (minusCutoff (action h (plusEmbedding (matrixNegativeTrunc g b))))) =
      (a,b) := by
  have hv : plusCutoff (action g (minusEmbedding b)) = matrixNegativeTrunc g b := by
    funext i
    simp [plusCutoff, action, minusEmbedding, matrixNegativeTrunc,
      negativeTruncMul, Matrix.mulVec, dotProduct, map_sum]
  apply Prod.ext
  · change polynomialAction p (plusCutoff (plusEmbedding a - action g (minusEmbedding b))) +
      polynomialAction p (matrixNegativeTrunc g b) = a
    rw [map_sub, plusCutoff_plusEmbedding, hv, map_sub, ha]
    abel
  · change -polynomialAction q (minusCutoff (action h
        (negativeRemainder (plusEmbedding a - action g (minusEmbedding b))))) +
      polynomialAction q (minusCutoff (action h (plusEmbedding (matrixNegativeTrunc g b)))) = b
    rw [map_sub, negativeRemainder_plusEmbedding, zero_sub, map_neg, map_neg, map_neg, neg_neg]
    rw [← map_add, ← map_add, ← map_add, ← hv]
    have he : negativeRemainder (action g (minusEmbedding b)) +
        plusEmbedding (plusCutoff (action g (minusEmbedding b))) =
          action g (minusEmbedding b) := sub_add_cancel _ _
    rw [he]
    have hh : action h (action g (minusEmbedding b)) =
        action (minusMatrix q) (minusEmbedding b) :=
      LinearMap.congr_fun ((action_mul h g).trans (congrArg action hhg)) _
    rw [hh, ← minusEmbedding_polynomialAction, hb, minusCutoff_minusEmbedding, hb]

end LaurentPolynomial.Projector

namespace LaurentPolynomial.Projector
open LaurentPolynomial.Cutoff
variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w}
variable [Fintype ι] [Fintype κ]

/-- The original signed differential restricted to the actual projector images. -/
def rangeDifference (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (g : Matrix ι κ R[T;T⁻¹]) (hp : p * p = p) (hpg : plusMatrix p * g = g) :
    (LinearMap.range (polynomialAction p) × LinearMap.range (polynomialAction q)) →ₗ[R]
      LinearMap.range (action (plusMatrix p)) :=
  ((difference g).comp
    (((LinearMap.range (polynomialAction p)).subtype.comp (LinearMap.fst R _ _)).prod
      ((LinearMap.range (polynomialAction q)).subtype.comp (LinearMap.snd R _ _)))).codRestrict
    (LinearMap.range (action (plusMatrix p))) (fun x => by
      refine ⟨difference g (x.1.val,x.2.val), ?_⟩
      change action (plusMatrix p)
        (plusEmbedding x.1.val - action g (minusEmbedding x.2.val)) =
          plusEmbedding x.1.val - action g (minusEmbedding x.2.val)
      rw [map_sub, ← plusEmbedding_polynomialAction, polynomialRange_fixed p hp]
      have he : action (plusMatrix p) (action g (minusEmbedding x.2.val)) =
          action g (minusEmbedding x.2.val) :=
        LinearMap.congr_fun ((action_mul _ _).trans (congrArg action hpg)) _
      rw [he])

/-- The original projected cutoff parametrix between the actual projector images. -/
def rangeParametrix (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (h : Matrix κ ι R[T;T⁻¹]) :
    LinearMap.range (action (plusMatrix p)) →ₗ[R]
      (LinearMap.range (polynomialAction p) × LinearMap.range (polynomialAction q)) :=
  (((polynomialAction p).rangeRestrict.comp plusCutoff).prod
    (- (polynomialAction q).rangeRestrict.comp
      (minusCutoff.comp ((action h).comp negativeRemainder)))).comp
        (LinearMap.range (action (plusMatrix p))).subtype

/-- Forgetting the image subtypes recovers the literal projected cutoff formula. -/
theorem rangeParametrix_val (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (h : Matrix κ ι R[T;T⁻¹]) (x : LinearMap.range (action (plusMatrix p))) :
    ((rangeParametrix p q h x).1.val, (rangeParametrix p q h x).2.val) =
      parametrix p q h x.val := rfl

end LaurentPolynomial.Projector
