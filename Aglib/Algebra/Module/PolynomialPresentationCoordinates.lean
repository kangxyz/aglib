/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.FinitePresentationCoordinates
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # Polynomial coordinates in a finite module presentation

Coordinates are chosen for the actual finitely many coefficients of the
polynomial. This construction does not require the presentation generators to
be linearly independent. Its evaluation formula is valid in every target
algebra, in particular in the completed-base tensor product.
-/

@[expose] public noncomputable section

open TensorProduct MvPolynomial
open scoped BigOperators

namespace Module.FinitePresentation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {d : ℕ} (f : (Fin d → R) →ₗ[R] A) (hf : Function.Surjective f)
variable {σ : Type*}

/-- Lift the actual coefficients on the support of a polynomial through a
surjective finite module presentation. -/
def polynomialCoordinates (p : MvPolynomial σ A) (a : Fin d) : MvPolynomial σ R :=
  ∑ m ∈ p.support, monomial m ((hf (p.coeff m)).choose a)

/-- A presentation is the linear combination of its actual standard generators. -/
theorem presentation_apply (z : Fin d → R) :
    f z = ∑ a, z a • f (Pi.single a 1) := by
  conv_lhs => rw [pi_eq_sum_univ' z]
  simp

/-- The chosen coordinates reconstruct the original polynomial, not merely a
polynomial with the same value at one particular tuple. -/
theorem polynomialCoordinates_reconstruct (p : MvPolynomial σ A) :
    (∑ a, C (f (Pi.single a 1)) *
      MvPolynomial.map (algebraMap R A) (polynomialCoordinates f hf p a)) = p := by
  classical
  ext m
  by_cases hm : m ∈ p.support
  · simp only [coeff_sum, coeff_C_mul, coeff_map, polynomialCoordinates,
      coeff_sum, coeff_monomial, Finset.sum_ite_eq', hm, ite_true]
    have h := (hf (p.coeff m)).choose_spec
    rw [presentation_apply] at h
    simpa only [Algebra.smul_def, mul_comm] using h
  · have hz : p.coeff m = 0 := by simpa using hm
    simp [polynomialCoordinates, hm, hz, coeff_C_mul]

/-- Evaluation commutes with the actual coefficient-coordinate reconstruction. -/
theorem eval₂_polynomialCoordinates
    {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (z : σ → B) (p : MvPolynomial σ A) :
    eval₂ φ.toRingHom z p =
      ∑ a, φ (f (Pi.single a 1)) *
        eval₂ (algebraMap R B) z (polynomialCoordinates f hf p a) := by
  conv_lhs => rw [← polynomialCoordinates_reconstruct f hf p]
  have hc : φ.toRingHom.comp (algebraMap R A) = algebraMap R B := by
    ext r
    exact φ.commutes r
  simp only [eval₂_sum, eval₂_mul, eval₂_C, eval₂_map, hc]
  rfl

/-- Scalar extension of polynomial evaluation is the tensor coordinate map. -/
theorem tensorCoordinates_eval₂
    {T : Type*} [CommRing T] [Algebra R T]
    (z : σ → T) (p : MvPolynomial σ A) :
    tensorCoordinates T f
      (fun a ↦ eval₂ (algebraMap R T) z (polynomialCoordinates f hf p a)) =
      eval₂ (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
        (fun j ↦ z j ⊗ₜ[R] (1 : A)) p := by
  rw [tensorCoordinates_apply, eval₂_polynomialCoordinates f hf]
  apply Finset.sum_congr rfl
  intro a ha
  let φ : T →ₐ[R] T ⊗[R] A := Algebra.TensorProduct.includeLeft
  have he := (polynomialCoordinates f hf p a).hom_eval₂
    (algebraMap R T) φ.toRingHom z
  have hc : φ.toRingHom.comp (algebraMap R T) = algebraMap R (T ⊗[R] A) := by
    ext r
    exact φ.commutes r
  rw [hc] at he
  change _ = (1 ⊗ₜ[R] f (Pi.single a 1)) *
    eval₂ (algebraMap R (T ⊗[R] A)) (fun j ↦ φ.toRingHom (z j)) _
  rw [← he]
  change _ = (1 ⊗ₜ[R] f (Pi.single a 1)) *
    (eval₂ (algebraMap R T) z (polynomialCoordinates f hf p a) ⊗ₜ[R] (1 : A))
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end Module.FinitePresentation
