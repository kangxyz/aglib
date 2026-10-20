/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Polynomial.Laurent.Cutoff
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Matrix.Basic

/-! # Actual finite Laurent-matrix cutoff factorizations

One finite window works uniformly for every entry and every negative-chart polynomial input.
The factor maps use the literal polynomial coefficients and the standard finite-window
inclusion. No finite-band or noetherianity hypothesis is assumed.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Polynomial/Laurent/MatrixCutoff.lean` from the
supplied frozen Quillen snapshot.
SHA-256: `fcc8a92e372ed93e07898888a8e8c974c1e2f3da0bd8a6edbc8dbc34b5ec7f3c`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
open Polynomial LaurentPolynomial
open scoped LaurentPolynomial
universe u v w
namespace LaurentPolynomial.Cutoff
variable {R : Type u} [CommRing R]

/-- Actual multiplication by one Laurent entry, with original negative-chart input and cutoff. -/
def negativeTruncMul (g : R[T;T⁻¹]) : R[X] →ₗ[R] R[X] :=
  (truncLinear R).comp ((LinearMap.mulLeft R g).comp
    (LaurentPolynomial.invert.toLinearMap.comp Polynomial.toLaurentAlg.toLinearMap))

/-- The actual finite Laurent matrix acts before taking each nonnegative cutoff. -/
def matrixNegativeTrunc {ι : Type v} {κ : Type w} [Fintype κ]
    (g : Matrix ι κ R[T;T⁻¹]) : (κ → R[X]) →ₗ[R] (ι → R[X]) :=
  LinearMap.pi fun i => ∑ j, (negativeTruncMul (g i j)).comp (LinearMap.proj j)

/-- All entries of an actual finite Laurent matrix admit one uniform finite output window. -/
theorem exists_matrix_negative_bound {ι : Type v} {κ : Type w} [Finite ι] [Fintype κ]
    (g : Matrix ι κ R[T;T⁻¹]) :
    ∃ N : ℕ, ∀ b : κ → R[X], ∀ i,
      matrixNegativeTrunc g b i ∈ Polynomial.degreeLT R N := by
  classical
  let := Fintype.ofFinite ι
  choose N hN using fun p : ι × κ => exists_trunc_negative_bound (g p.1 p.2)
  refine ⟨Finset.univ.sup N, fun b i => ?_⟩
  simp only [matrixNegativeTrunc, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  apply Submodule.sum_mem
  intro j _
  exact Polynomial.degreeLT_mono (Finset.le_sup (by simp : (i,j) ∈ Finset.univ))
    (hN (i,j) (b j))

/-- Original coefficient inclusion of the finite polynomial window. -/
def windowInclusion (N : ℕ) : (Fin N → R) →ₗ[R] R[X] :=
  (Polynomial.degreeLT R N).subtype.comp (Polynomial.degreeLTEquiv R N).symm.toLinearMap

/-- The exact coefficients of the original cutoff, using its proved uniform bound. -/
def matrixWindowCoefficients {ι : Type v} {κ : Type w} [Fintype κ]
    (g : Matrix ι κ R[T;T⁻¹]) (N : ℕ)
    (hN : ∀ b : κ → R[X], ∀ i, matrixNegativeTrunc g b i ∈ Polynomial.degreeLT R N) :
    (κ → R[X]) →ₗ[R] (ι → Fin N → R) :=
  LinearMap.pi fun i => (Polynomial.degreeLTEquiv R N).toLinearMap.comp
    (((LinearMap.proj i).comp (matrixNegativeTrunc g)).codRestrict
      (Polynomial.degreeLT R N) (fun b => hN b i))

/-- The literal matrix cutoff factors through the finite coefficient window. -/
theorem matrix_window_factorization {ι : Type v} {κ : Type w} [Fintype κ]
    (g : Matrix ι κ R[T;T⁻¹]) (N : ℕ)
    (hN : ∀ b : κ → R[X], ∀ i, matrixNegativeTrunc g b i ∈ Polynomial.degreeLT R N)
    (b : κ → R[X]) (i : ι) :
    windowInclusion N (matrixWindowCoefficients g N hN b i) = matrixNegativeTrunc g b i := by
  exact congrArg Subtype.val ((Polynomial.degreeLTEquiv R N).symm_apply_apply
    ⟨matrixNegativeTrunc g b i, hN b i⟩)

end LaurentPolynomial.Cutoff
