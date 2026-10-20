/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Polynomial.Laurent.MatrixCech
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Actual polynomial projector images and Laurent chart actions

The rectangular matrix actions preserve the original positive and negative restrictions.
An idempotent polynomial matrix has an actual base-ring-projective image via its literal
range inclusion and projector retraction. No freeness or noetherianity is assumed.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Polynomial/Laurent/MatrixProjector.lean` from the
supplied frozen Quillen snapshot.
SHA-256: `bdbcb2b86f5f5c6747b02572ed986ac3671da02309bcd1e3442f388d1778e3f3`.
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

/-- The actual rectangular Laurent-matrix action on coefficient vectors. -/
def action {ι : Type v} {κ : Type w} [Fintype κ]
    (g : Matrix ι κ R[T;T⁻¹]) : (κ → R[T;T⁻¹]) →ₗ[R] (ι → R[T;T⁻¹]) :=
  g.mulVecLin.restrictScalars R

/-- The actual polynomial-matrix action, regarded over the base ring. -/
def polynomialAction {ι : Type v} {κ : Type w} [Fintype κ]
    (g : Matrix ι κ R[X]) : (κ → R[X]) →ₗ[R] (ι → R[X]) :=
  g.mulVecLin.restrictScalars R

/-- The polynomial matrix restricted to the positive Laurent chart. -/
def plusMatrix {ι : Type v} {κ : Type w} (p : Matrix ι κ R[X]) :
    Matrix ι κ R[T;T⁻¹] := p.map toLaurent

/-- The polynomial matrix restricted to the negative Laurent chart. -/
def minusMatrix {ι : Type v} {κ : Type w} (p : Matrix ι κ R[X]) :
    Matrix ι κ R[T;T⁻¹] := p.map (fun x => invert (toLaurent x))

/-- The rectangular linear actions retain original matrix multiplication. -/
theorem action_mul {ι : Type v} {κ : Type w} {ν : Type z} [Fintype κ] [Fintype ν]
    (g : Matrix ι κ R[T;T⁻¹]) (h : Matrix κ ν R[T;T⁻¹]) :
    (action g).comp (action h) = action (g * h) := by
  apply LinearMap.ext
  intro x
  exact Matrix.mulVec_mulVec x g h

/-- The positive restriction intertwines the original polynomial and Laurent actions. -/
theorem plusEmbedding_polynomialAction {ι : Type v} {κ : Type w} [Fintype κ]
    (p : Matrix ι κ R[X]) (a : κ → R[X]) :
    plusEmbedding (polynomialAction p a) = action (plusMatrix p) (plusEmbedding a) := by
  funext i
  change toLaurent (∑ j, p i j * a j) = ∑ j, toLaurent (p i j) * toLaurent (a j)
  simp only [map_sum, map_mul]

/-- The negative restriction intertwines the original polynomial and Laurent actions. -/
theorem minusEmbedding_polynomialAction {ι : Type v} {κ : Type w} [Fintype κ]
    (p : Matrix ι κ R[X]) (a : κ → R[X]) :
    minusEmbedding (polynomialAction p a) = action (minusMatrix p) (minusEmbedding a) := by
  funext i
  change invert (toLaurent (∑ j, p i j * a j)) =
    ∑ j, invert (toLaurent (p i j)) * invert (toLaurent (a j))
  simp only [map_sum, map_mul]

end LaurentPolynomial.Projector

namespace LaurentPolynomial.Projector
variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι]

/-- Polynomial linear actions retain original matrix multiplication. -/
theorem polynomialAction_mul (p q : Matrix ι ι R[X]) :
    (polynomialAction p).comp (polynomialAction q) = polynomialAction (p * q) := by
  apply LinearMap.ext
  intro x
  exact Matrix.mulVec_mulVec x p q

/-- Every element of an actual idempotent polynomial image is fixed by its projector. -/
theorem polynomialRange_fixed (p : Matrix ι ι R[X]) (hp : p * p = p)
    (x : LinearMap.range (polynomialAction p)) : polynomialAction p x.val = x.val := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact LinearMap.congr_fun ((polynomialAction_mul p p).trans
    (congrArg polynomialAction hp)) y

/-- The actual polynomial projector image is projective over the base ring by retraction. -/
theorem polynomialRange_projective (p : Matrix ι ι R[X]) (hp : p * p = p) :
    Module.Projective R (LinearMap.range (polynomialAction p)) := by
  apply Module.Projective.of_split (LinearMap.range (polynomialAction p)).subtype
    (polynomialAction p).rangeRestrict
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact polynomialRange_fixed p hp x

end LaurentPolynomial.Projector

namespace LaurentPolynomial.Projector
open LaurentPolynomial.Cutoff
variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w}
variable [Fintype ι] [Fintype κ]

/-- The positive chart matrix map preserves the original product. -/
theorem plusMatrix_mul (p q : Matrix ι ι R[X]) :
    plusMatrix (p * q) = plusMatrix p * plusMatrix q := by
  ext i j
  simp [plusMatrix, Matrix.mul_apply, map_sum, map_mul]

/-- Every element of the localized polynomial projector image is fixed by its projector. -/
theorem laurentRange_fixed (p : Matrix ι ι R[X]) (hp : p * p = p)
    (x : LinearMap.range (action (plusMatrix p))) : action (plusMatrix p) x.val = x.val := by
  obtain ⟨y, hy⟩ := x.property
  have he : plusMatrix p * plusMatrix p = plusMatrix p :=
    (plusMatrix_mul p p).symm.trans (congrArg (fun t : Matrix ι ι R[X] => plusMatrix t) hp)
  calc
    action (plusMatrix p) x.val = action (plusMatrix p) (action (plusMatrix p) y) :=
      congrArg (action (plusMatrix p)) hy.symm
    _ = action (plusMatrix p * plusMatrix p) y :=
      LinearMap.congr_fun (action_mul (plusMatrix p) (plusMatrix p)) y
    _ = action (plusMatrix p) y := congrArg (fun t : Matrix ι ι R[T;T⁻¹] => action t y) he
    _ = x.val := hy

end LaurentPolynomial.Projector
