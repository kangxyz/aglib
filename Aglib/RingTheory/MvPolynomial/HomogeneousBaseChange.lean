/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.CoordinatePieces
public import Aglib.RingTheory.MvPolynomial.GradedMap
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of homogeneous components

For an `A`-algebra `B`, `homogeneousSubmoduleBaseChangeEquiv σ m A B : B ⊗[A] A[x]_m ≃ₗ[B] B[x]_m`
is built from the monomial coordinates `homogeneousPieceEquivFinsupp` on both sides and
`TensorProduct.finsuppScalarRight`.

* `coeff_homogeneousPieceEquivFinsupp_symm`: the coefficients of the homogeneous polynomial with
  given monomial coordinates.
* `homogeneousSubmoduleBaseChangeEquiv_tmul`: `b ⊗ q ↦ b • q`, with coefficients mapped to `B`.
* `homogeneousSubmoduleBaseChangeEquiv_rTensor`: for an `A`-algebra map `f : B → B'`, `f ⊗ id`
  is the coefficient map `(gradedMap f).gradedAddHom m : B[x]_m → B'[x]_m`.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace MvPolynomial

variable (σ : Type u) (m : ℕ)

/-- **Base change of homogeneous components**: `B ⊗[A] A[x]_m ≃ₗ[B] B[x]_m`, through the monomial
coordinates `homogeneousPieceEquivFinsupp`. -/
def homogeneousSubmoduleBaseChangeEquiv (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    B ⊗[A] homogeneousSubmodule σ A m ≃ₗ[B] homogeneousSubmodule σ B m := by
  classical
  exact ((homogeneousPieceEquivFinsupp (ι := σ) A m).baseChange A B _ _).trans
    ((TensorProduct.finsuppScalarRight A B B {d : σ →₀ ℕ // d.degree = m}).trans
      (homogeneousPieceEquivFinsupp (ι := σ) B m).symm)

/-- The coefficients of a homogeneous polynomial given by its coefficients on the monomials of
degree `m`. -/
theorem coeff_homogeneousPieceEquivFinsupp_symm (R : Type u) [CommRing R]
    (c : {d : σ →₀ ℕ // d.degree = m} →₀ R) (d : σ →₀ ℕ) :
    ((homogeneousPieceEquivFinsupp (ι := σ) R m).symm c).1.coeff d =
      if h : d.degree = m then c ⟨d, h⟩ else 0 := by
  split_ifs with h
  · exact congrArg (fun g => g ⟨d, h⟩)
      ((homogeneousPieceEquivFinsupp (ι := σ) R m).apply_symm_apply c)
  · have hp := (mem_homogeneousSubmodule _ _).mp
      ((homogeneousPieceEquivFinsupp (ι := σ) R m).symm c).2
    by_contra hne
    exact h (by rw [Finsupp.degree_eq_weight_one]; exact hp hne)

/-- `B ⊗[A] A[x]_m ≃ₗ[B] B[x]_m` sends `b ⊗ q` to `b • q`, with coefficients mapped to `B`. -/
theorem homogeneousSubmoduleBaseChangeEquiv_tmul (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (b : B) (q : homogeneousSubmodule σ A m) :
    (homogeneousSubmoduleBaseChangeEquiv σ m A B (b ⊗ₜ q)).1 = b • map (algebraMap A B) q.1 := by
  classical
  ext d
  rw [homogeneousSubmoduleBaseChangeEquiv]
  simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  erw [coeff_homogeneousPieceEquivFinsupp_symm]
  split_ifs with h
  · erw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
    rw [coeff_smul, coeff_map, smul_eq_mul, Algebra.smul_def, mul_comm]
    rfl
  · have hq : q.1.coeff d = 0 := by
      have := (mem_homogeneousSubmodule _ _).mp q.2
      by_contra hne
      exact h (by rw [Finsupp.degree_eq_weight_one]; exact this hne)
    simp [coeff_map, hq]

/-- **Base change of homogeneous components is natural**: under `B ⊗[A] A[x]_m ≃ B[x]_m`, the
map `f ⊗ id` for an `A`-algebra map `f : B → B'` is the coefficient map
`(gradedMap f).gradedAddHom m : B[x]_m → B'[x]_m`. -/
theorem homogeneousSubmoduleBaseChangeEquiv_rTensor (A B B' : Type u) [CommRing A] [CommRing B]
    [CommRing B'] [Algebra A B] [Algebra A B'] (f : B →ₐ[A] B')
    (x : B ⊗[A] homogeneousSubmodule σ A m) :
    homogeneousSubmoduleBaseChangeEquiv σ m A B' (f.toLinearMap.rTensor _ x) =
      (gradedMap (ι := σ) (f : B →+* B')).gradedAddHom m
        (homogeneousSubmoduleBaseChangeEquiv σ m A B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b q =>
    apply Subtype.ext
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    change _ = map (f : B →+* B') (homogeneousSubmoduleBaseChangeEquiv σ m A B (b ⊗ₜ q)).1
    rw [homogeneousSubmoduleBaseChangeEquiv_tmul, homogeneousSubmoduleBaseChangeEquiv_tmul,
      smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, map_map, AlgHom.comp_algebraMap]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end MvPolynomial
