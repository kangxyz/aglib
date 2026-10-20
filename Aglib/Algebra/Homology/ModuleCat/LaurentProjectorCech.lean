/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Polynomial.Laurent.ProjectorFiniteDefects
public import Aglib.Algebra.Homology.ModuleCat.LinearMapConeShift

/-! # Finite-projective Cech models for polynomial projector charts

Actual idempotent polynomial matrices and compatible rectangular Laurent transitions
give a finite-projective model of the original image-module differential. Both finite-window
bounds are proved, and the degree-zero/one model retains the explicit signed cone shift.
Presenting arbitrary geometric chart modules and identifying their transition maps remain
separate obligations.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Homology/ModuleCat/LaurentProjectorCech.lean` from
the supplied frozen Quillen snapshot.
SHA-256: `ac0d9b698631502024cf88b383617c5354f60909fbd34251420f8ca18bc7d373`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Polynomial LaurentPolynomial
open scoped LaurentPolynomial Matrix
universe u v w z
namespace LaurentPolynomial.Projector
open LaurentPolynomial.Cutoff ModuleCat
variable {R : Type u} [CommRing R] {ι κ : Type v} [Fintype ι] [Fintype κ]

/-- Actual compatible polynomial projectors and Laurent transition maps give a finite-
projective cone model. -/
theorem exists_projector_cone_model (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (g : Matrix ι κ R[T;T⁻¹]) (h : Matrix κ ι R[T;T⁻¹])
    (hp : p * p = p) (hq : q * q = q) (hpg : plusMatrix p * g = g)
    (hgh : g * h = plusMatrix p) (hhg : h * g = minusMatrix q)
    (hgq : g * minusMatrix q = g) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∀ n, n ≠ -1 → n ≠ 0 → IsZero (P.X n)) ∧
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      Nonempty (HomotopyEquiv (linearMapCone (rangeDifference p q g hp hpg)) P) := by
  have := polynomialRange_projective p hp
  have := polynomialRange_projective q hq
  obtain ⟨N, hN⟩ := exists_matrix_negative_bound g
  obtain ⟨M, hM⟩ := exists_matrix_negative_bound h
  exact exists_finite_projective_parametrix_model (rangeDifference p q g hp hpg)
    (rangeParametrix p q h) (rangeRightWindow p g hpg M) (rangeRightCoefficients p h M hM)
    (range_right_identity p q g h hp hpg hgh hgq M hM)
    (rangeLeftWindow p q h N) (rangeLeftCoefficients p q g N hN)
    (range_left_identity p q g h hp hq hpg hhg N hN)

/-- The same actual projector-image differential has a finite-projective model in degrees zero
and one. -/
theorem exists_projector_cech_model (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (g : Matrix ι κ R[T;T⁻¹]) (h : Matrix κ ι R[T;T⁻¹])
    (hp : p * p = p) (hq : q * q = q) (hpg : plusMatrix p * g = g)
    (hgh : g * h = plusMatrix p) (hhg : h * g = minusMatrix q)
    (hgq : g * minusMatrix q = g) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∀ n, n ≠ 0 → n ≠ 1 → IsZero (P.X n)) ∧
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex (rangeDifference p q g hp hpg)) P) := by
  obtain ⟨P, hP, hf, ⟨e⟩⟩ := exists_projector_cone_model p q g h hp hq hpg hgh hhg hgq
  refine ⟨P⟦(-1 : ℤ)⟧, ?_, ?_, ?_⟩
  · intro n h0 h1
    exact hP (n + -1) (by omega) (by omega)
  · intro n
    exact hf (n + -1)
  · refine ⟨{
      hom := e.hom⟦(-1 : ℤ)⟧'
      inv := e.inv⟦(-1 : ℤ)⟧'
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }⟩
    · simpa only [linearMapCechComplex, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_id] using e.homotopyHomInvId.shift (-1)
    · simpa only [linearMapCechComplex, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_id] using e.homotopyInvHomId.shift (-1)

end LaurentPolynomial.Projector
